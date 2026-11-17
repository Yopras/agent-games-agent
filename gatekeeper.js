// Proof Gatekeeper arena handler — Agent Games zkVerify, Season 01.
//
// Implements the Proof Gatekeeper track end to end:
//   signed task envelope in -> deterministic APPROVE/REJECT decision ->
//   real Groth16 proof of that decision, generated locally with snarkjs and
//   the OFFICIAL gatekeeper circuit (circuits/gatekeeper.wasm +
//   gatekeeper_final.zkey, vkHash 0x6b79c6...d77b0), verified locally
//   before the response is returned.
//
// Sources (researched 2026-11-17, see ARENA_BUILD_STATUS.md):
//  - Official /build + /rules + /api/circuit-info: envelope is signed JSON,
//    60s hard deadline, HTTPS public endpoint, HMAC both directions,
//    task IDs are idempotency keys.
//  - Official event-page payload sample (quoted by multiple entrants):
//      { "type": "agent-games.proof-gatekeeper.v1", "task_id": "gk_24_9d1",
//        "input": { registered_vk, proof_vk, minimum, public_balance,
//                   expiry_block, current_block, recipient,
//                   condition_recipient, amount, max_transfer, proof_tx } }
//  - The circuit's 13 inputs are NOT published by the platform; they were
//    recovered by entrants probing the WASM input table and are corroborated
//    by several independent build write-ups + live practice results:
//      registeredVkHash, proofVkHash, minimum, publicBalance, expiryBlock,
//      currentBlock, recipient, conditionRecipient, amount, maxTransfer,
//      decision (1=APPROVE, 0=REJECT), taskId, salt (private).
//    Public signals (13): [Poseidon(salt, taskId), then the 12 public fields
//    in the order above minus salt]. taskId is mapped as
//    keccak256(utf8(task_id)) mod p — confirmed correct by a live entrant's
//    practice rounds (9/9 proofs verified by the platform).
//  - Decision checklist, fixed order, first failure is the reason code:
//      VK_SUBSTITUTION (proof_vk != registered_vk)
//      PROOF_REUSED    (same proof_tx under a DIFFERENT task_id; a retry of
//                       the same task is not reuse)
//      THRESHOLD_MISMATCH (public_balance < minimum; equal is valid)
//      EXPIRED_CONDITION  (current_block >= expiry_block; equal is expired)
//      RECIPIENT_MISMATCH (recipient != condition_recipient)
//      AMOUNT_OVERFLOW    (amount > max_transfer; equal is valid)
//      VALID_CONDITION    -> APPROVE
//    Scoring: correct +12, wrong APPROVE -6, wrong REJECT -3,
//    timeout / missing proof -2.
//  - The circuit enforces decision == computed verdict: a wrong decision
//    cannot even build a witness (assert in GatekeeperEvaluation). So the
//    checklist above must mirror the circuit exactly; if proving the chosen
//    decision ever fails, NO proof exists for the other decision either and
//    the decision is returned without a proof (visible -2, never a hang).
//  - PROOF_REUSED responses carry no proof (platform convention reported by
//    a live entrant; reused answers are excluded from the reliability bonus).
//
// Steal the VFY is intentionally NOT implemented here (different circuit,
// strategy commitment required before Swiss Round 1) — server.js keeps it
// fail-closed.

'use strict';
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const BN128_PRIME = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
const CIRCUITS_DIR = __dirname;
const WASM_PATH = path.join(CIRCUITS_DIR, 'gatekeeper.wasm');
const ZKEY_PATH = path.join(CIRCUITS_DIR, 'gatekeeper_final.zkey');
const VK_PATH = path.join(CIRCUITS_DIR, 'gatekeeper_verification_key.json');

let snarkjs = null;
let verificationKey = null;
function loadProver() {
  if (!snarkjs) {
    snarkjs = require('snarkjs');
    verificationKey = JSON.parse(fs.readFileSync(VK_PATH, 'utf8'));
  }
  return snarkjs;
}

// ---------------------------------------------------------------------------
// keccak256 (original Keccak padding, NOT NIST SHA3-256) — pure JS, BigInt
// lanes. Node's crypto offers sha3-256 but not keccak-256, and the taskId
// mapping needs real keccak. Validated against published test vectors in
// test/gatekeeper.test.js (keccak256("") and keccak256("abc")).
// ---------------------------------------------------------------------------
const MASK64 = (1n << 64n) - 1n;
const KECCAK_RC = [
  0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n,
  0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n,
  0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an,
  0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n,
  0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an,
  0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n,
];
// Rotation offsets r[x][y], lane index = x + 5*y.
const KECCAK_ROT = [
  [0, 36, 3, 41, 18],
  [1, 44, 10, 45, 2],
  [62, 6, 43, 15, 61],
  [28, 55, 25, 21, 56],
  [27, 20, 39, 8, 14],
];
function rotl64(x, n) {
  if (n === 0) return x;
  const b = BigInt(n);
  return ((x << b) | (x >> (64n - b))) & MASK64;
}
function keccakF1600(state) {
  const C = new Array(5);
  const D = new Array(5);
  const B = new Array(25);
  for (let round = 0; round < 24; round++) {
    // theta
    for (let x = 0; x < 5; x++) C[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    for (let x = 0; x < 5; x++) D[x] = C[(x + 4) % 5] ^ rotl64(C[(x + 1) % 5], 1);
    for (let i = 0; i < 25; i++) state[i] ^= D[i % 5];
    // rho + pi
    for (let x = 0; x < 5; x++) {
      for (let y = 0; y < 5; y++) {
        B[y + 5 * ((2 * x + 3 * y) % 5)] = rotl64(state[x + 5 * y], KECCAK_ROT[x][y]);
      }
    }
    // chi
    for (let x = 0; x < 5; x++) {
      for (let y = 0; y < 5; y++) {
        state[x + 5 * y] = B[x + 5 * y] ^ ((~B[((x + 1) % 5) + 5 * y] & MASK64) & B[((x + 2) % 5) + 5 * y]);
      }
    }
    // iota
    state[0] ^= KECCAK_RC[round];
  }
}
function keccak256(data) {
  const rate = 136; // 1088-bit rate for 256-bit output
  const state = new Array(25).fill(0n);
  const input = Buffer.isBuffer(data) ? data : Buffer.from(String(data), 'utf8');
  const padded = Buffer.alloc(Math.ceil((input.length + 1) / rate) * rate, 0);
  input.copy(padded, 0);
  padded[input.length] = 0x01; // Keccak pad10*1 starts with 0x01 (SHA3 uses 0x06)
  padded[padded.length - 1] |= 0x80;
  for (let off = 0; off < padded.length; off += rate) {
    for (let lane = 0; lane < rate / 8; lane++) {
      let v = 0n;
      for (let b = 0; b < 8; b++) v |= BigInt(padded[off + lane * 8 + b]) << BigInt(8 * b);
      state[lane] ^= v;
    }
    keccakF1600(state);
  }
  const out = Buffer.alloc(32);
  for (let lane = 0; lane < 4; lane++) {
    let v = state[lane];
    for (let b = 0; b < 8; b++) { out[lane * 8 + b] = Number(v & 0xffn); v >>= 8n; }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Field mapping helpers. All circuit inputs are decimal strings of field
// elements. Values may arrive as numbers, decimal strings, or 0x-hex strings.
// ---------------------------------------------------------------------------
function parseInteger(value, fieldName) {
  if (typeof value === 'number') {
    if (!Number.isSafeInteger(value)) throw new Error(`field ${fieldName}: unsafe number`);
    return BigInt(value);
  }
  if (typeof value === 'bigint') return value;
  if (typeof value === 'string' && value.trim() !== '') {
    const s = value.trim();
    try { return BigInt(s); } catch { /* fall through */ }
  }
  throw new Error(`field ${fieldName}: not an integer value`);
}
function toFieldString(big) {
  const r = ((big % BN128_PRIME) + BN128_PRIME) % BN128_PRIME;
  return r.toString(10);
}
// VK hashes are 256-bit keccak values; reduce mod the BN128 scalar prime.
function vkHashToField(value, fieldName) {
  return toFieldString(parseInteger(value, fieldName));
}
// Task IDs are strings like "gk_24_9d1": keccak256(utf8(task_id)) mod p.
// (Confirmed against live practice rounds by an independent entrant.)
function taskIdToField(taskId) {
  const digest = keccak256(Buffer.from(String(taskId), 'utf8'));
  return toFieldString(BigInt('0x' + digest.toString('hex')));
}
function randomSalt() {
  return toFieldString(BigInt('0x' + crypto.randomBytes(32).toString('hex')));
}

// ---------------------------------------------------------------------------
// Decision checklist — fixed order, first failure wins. Mirrors the circuit.
// ---------------------------------------------------------------------------
const seenProofTx = new Map(); // proof_tx -> task_id that first presented it
const responseCache = new Map(); // task_id -> response body (idempotent retries)

function decide(flat) {
  const registeredVk = parseInteger(flat.registered_vk, 'registered_vk');
  const proofVk = parseInteger(flat.proof_vk, 'proof_vk');
  if (registeredVk !== proofVk) return { decision: 'REJECT', reason_code: 'VK_SUBSTITUTION' };

  if (flat.proof_tx != null && flat.proof_tx !== '') {
    const key = String(flat.proof_tx).toLowerCase();
    const firstTask = seenProofTx.get(key);
    if (firstTask !== undefined && firstTask !== String(flat.task_id)) {
      return { decision: 'REJECT', reason_code: 'PROOF_REUSED' };
    }
    if (firstTask === undefined) seenProofTx.set(key, String(flat.task_id));
  }

  const minimum = parseInteger(flat.minimum, 'minimum');
  const publicBalance = parseInteger(flat.public_balance, 'public_balance');
  if (publicBalance < minimum) return { decision: 'REJECT', reason_code: 'THRESHOLD_MISMATCH' };

  const expiryBlock = parseInteger(flat.expiry_block, 'expiry_block');
  const currentBlock = parseInteger(flat.current_block, 'current_block');
  if (currentBlock >= expiryBlock) return { decision: 'REJECT', reason_code: 'EXPIRED_CONDITION' };

  const recipient = parseInteger(flat.recipient, 'recipient');
  const conditionRecipient = parseInteger(flat.condition_recipient, 'condition_recipient');
  if (recipient !== conditionRecipient) return { decision: 'REJECT', reason_code: 'RECIPIENT_MISMATCH' };

  const amount = parseInteger(flat.amount, 'amount');
  const maxTransfer = parseInteger(flat.max_transfer, 'max_transfer');
  if (amount > maxTransfer) return { decision: 'REJECT', reason_code: 'AMOUNT_OVERFLOW' };

  return { decision: 'APPROVE', reason_code: 'VALID_CONDITION' };
}

function buildCircuitInput(flat, decision) {
  return {
    registeredVkHash: vkHashToField(flat.registered_vk, 'registered_vk'),
    proofVkHash: vkHashToField(flat.proof_vk, 'proof_vk'),
    minimum: toFieldString(parseInteger(flat.minimum, 'minimum')),
    publicBalance: toFieldString(parseInteger(flat.public_balance, 'public_balance')),
    expiryBlock: toFieldString(parseInteger(flat.expiry_block, 'expiry_block')),
    currentBlock: toFieldString(parseInteger(flat.current_block, 'current_block')),
    recipient: toFieldString(parseInteger(flat.recipient, 'recipient')),
    conditionRecipient: toFieldString(parseInteger(flat.condition_recipient, 'condition_recipient')),
    amount: toFieldString(parseInteger(flat.amount, 'amount')),
    maxTransfer: toFieldString(parseInteger(flat.max_transfer, 'max_transfer')),
    decision: decision === 'APPROVE' ? '1' : '0',
    taskId: taskIdToField(flat.task_id),
    salt: randomSalt(),
  };
}

async function proveDecision(flat, decision) {
  const snark = loadProver();
  const input = buildCircuitInput(flat, decision);
  const { proof, publicSignals } = await snark.groth16.fullProve(input, WASM_PATH, ZKEY_PATH);
  const ok = await snark.groth16.verify(verificationKey, publicSignals, proof);
  if (!ok) throw new Error('local verification of generated proof failed');
  return { proof, publicSignals };
}

// Main entry: takes the parsed task envelope, returns the response body.
// Never throws for task-level problems — fail closed with a REJECT instead.
async function handleGatekeeperTask(task) {
  const taskId = task && task.task_id != null ? String(task.task_id) : null;
  if (taskId && responseCache.has(taskId)) return responseCache.get(taskId);

  const input = task && typeof task.input === 'object' && task.input ? task.input : {};
  const flat = { ...input, task_id: task ? task.task_id : undefined };
  const out = {};

  let verdict;
  try {
    verdict = decide(flat);
  } catch (err) {
    // Missing/unparseable fields: no circuit input can be built, so no proof
    // can exist. Fail closed with a REJECT (reason code is a local label —
    // the official codes cover well-formed tasks only).
    out.decision = 'REJECT';
    out.reason_code = 'MALFORMED_TASK';
    out.proof_error = String(err && err.message ? err.message : err);
    if (taskId) responseCache.set(taskId, out);
    return out;
  }

  out.decision = verdict.decision;
  out.reason_code = verdict.reason_code;
  if (flat.proof_tx != null && flat.proof_tx !== '') out.proof_tx = flat.proof_tx;

  if (verdict.reason_code !== 'PROOF_REUSED') {
    try {
      const { proof, publicSignals } = await proveDecision(flat, verdict.decision);
      out.proof = proof;
      out.public_signals = publicSignals;
    } catch (err) {
      // The circuit only proves the correct decision; if proving failed we
      // cannot switch decisions (that proof cannot exist either). Return the
      // decision without a proof — a visible failure, never a hang or a
      // fabricated approval.
      console.error('[gatekeeper] proof failed for', taskId, err && err.message ? err.message : err);
      out.proof_error = 'proof generation failed';
    }
  }

  if (taskId) responseCache.set(taskId, out);
  return out;
}

module.exports = {
  handleGatekeeperTask,
  // exported for tests
  _internal: { keccak256, taskIdToField, decide, buildCircuitInput, BN128_PRIME },
};
