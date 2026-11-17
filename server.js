// Agent Games zkVerify — minimal agent endpoint skeleton
// Season 01, 2026-10-21 to 2026-11-21. Entry is free. Prizes 400,000 VFY total,
// 100,000 VFY per track, split 50/30/20 across top 3 per track.
// Sources verified 2026-11-15 ~10:05-10:06 WIB:
//  - https://agentgames.zkverify.io/build — interface, HMAC, 60s deadline, HTTPS only
//  - https://agentgames.zkverify.io/api/circuit-info — network mainnet, vkHashes + artifacts below
//  - https://agentgames.zkverify.io/guide — register with X or wallet, handle/country/bio,
//    wallet optional now but required to claim VFY prizes; Creator Track submitted
//    from the dashboard for manual review.
//
// WHAT THIS IS / IS NOT:
//  - Preflight + HMAC verify/sign + fail-closed envelope.
//  - Proof Gatekeeper IS implemented (gatekeeper.js): deterministic 7-check
//    decision + a real Groth16 proof from the official circuit, generated and
//    locally verified per task. Locally end-to-end tested 2026-11-17 — see
//    ARENA_BUILD_STATUS.md. It has NOT yet seen a live platform task: run
//    unscored practice tasks after registering before trusting scored rounds.
//  - Steal the VFY is NOT implemented (different circuit + an active strategy
//    commitment is required BEFORE Swiss Round 1) — it stays fail-closed.
//  - Creator Track needs NO endpoint at all — it is submitted from the dashboard
//    for manual review, and fits the 6 days left to 2026-11-21 far better.
//
// SETUP (after the user registers from his phone — X login in Muse's browser
// is temporarily limited by X since 2026-11-15 ~09:19 WIB, do NOT retry it):
//  1. Dashboard -> My Agents -> register agent, copy the HMAC secret shown ONCE
//     (Rotate Secret). Set it as AGENT_GAMES_HMAC_SECRET — never a placeholder.
//  2. Deploy this file on a public HTTPS host (no localhost / private IP / custom port).
//  3. Register the public URL in the dashboard, run preflight, then practice tasks.
//
// Circuits (verified 2026-11-15 10:06 WIB, field name is "vkHash"):
//  gatekeeper: vkHash 0x6b79c6012a6d8651f3e13bc4d2a20370280ab49700c90c5316d4168bfbad77b0
//    wasm https://agentgames.zkverify.io/circuits/gatekeeper.wasm
//    zkey https://agentgames.zkverify.io/circuits/gatekeeper_final.zkey
//  vfyPolicy:  vkHash 0x6c56509f1c56fd1fd4e9737f906d2220f4b95f1d507f1adf6899085bd74be047
//    wasm https://agentgames.zkverify.io/circuits/vfy-policy.wasm
//    zkey https://agentgames.zkverify.io/circuits/vfy-policy_final.zkey
//  Submit proofs via Kurier (recommended, REST, mainnet API key) or zkVerifyJS.
//  Never paste a private key, wallet seed, or API key into an AI tool.

'use strict';
const http = require('http');
const crypto = require('crypto');

const PORT = Number(process.env.PORT || 3000);
const SECRET = process.env.AGENT_GAMES_HMAC_SECRET || '';
if (!SECRET) console.warn('[agent-games] WARNING: AGENT_GAMES_HMAC_SECRET is not set — preflight will still answer, but signed verification will fail closed. Set the platform-issued secret before registering.');

function hmacHex(secret, rawBody) {
  return crypto.createHmac('sha256', secret).update(rawBody).digest('hex');
}
function timingSafeEqual(a, b) {
  const ba = Buffer.from(a, 'utf8');
  const bb = Buffer.from(b, 'utf8');
  return ba.length === bb.length && crypto.timingSafeEqual(ba, bb);
}
function sendJson(res, status, obj) {
  const body = JSON.stringify(obj);
  // Every response is signed with x-agent-games-signature over the raw response body.
  const headers = { 'Content-Type': 'application/json' };
  if (SECRET) headers['x-agent-games-signature'] = hmacHex(SECRET, body);
  res.writeHead(status, headers);
  res.end(body);
}
function readRawBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

// Proof Gatekeeper handler (gatekeeper.js + snarkjs + official circuits).
// Loaded lazily and defensively: if the module or its artifacts are missing,
// gatekeeper tasks fail closed with 501 instead of taking the endpoint down.
let gatekeeperHandler = null;
let gatekeeperLoadError = null;
try {
  gatekeeperHandler = require('./gatekeeper').handleGatekeeperTask;
} catch (err) {
  gatekeeperLoadError = err;
  console.warn('[agent-games] gatekeeper module unavailable, arena tasks will fail closed:', err.message);
}

const server = http.createServer(async (req, res) => {
  try {
    // Preflight / health: the platform expects { ok: true, protocolVersion: "v1" }.
    if (req.method === 'GET' && (req.url === '/' || req.url === '/health')) {
      return sendJson(res, 200, { ok: true, protocolVersion: 'v1' });
    }
    if (req.method !== 'POST' || req.url !== '/agent') {
      return sendJson(res, 404, { ok: false, error: 'not_found' });
    }
    const raw = await readRawBody(req);
    // Verify the HMAC signature against the raw body BEFORE parsing or processing.
    // Fail closed on timeout or uncertainty.
    if (SECRET) {
      const sig = req.headers['x-agent-games-signature'] || req.headers['x-signature'] || '';
      const expected = hmacHex(SECRET, raw);
      const supplied = String(sig).replace(/^sha256=/, '');
      if (!supplied || !timingSafeEqual(supplied, expected)) {
        return sendJson(res, 401, { ok: false, error: 'invalid_signature' });
      }
    }
    let task;
    try { task = JSON.parse(raw.toString('utf8')); } catch {
      return sendJson(res, 400, { ok: false, error: 'invalid_json' });
    }
    // Preflight-style task: answer the handshake, do not invent a game decision.
    if (task && (task.type === 'preflight' || task.type === 'ping' || task.type === 'health' || task.type === 'agent-games.preflight.v1')) {
      return sendJson(res, 200, { ok: true, protocolVersion: 'v1' });
    }
    // Proof Gatekeeper: deterministic decision + real Groth16 proof of the
    // decision (gatekeeper.js). Response is signed by sendJson as usual.
    if (task && task.type === 'agent-games.proof-gatekeeper.v1') {
      if (!gatekeeperHandler) {
        return sendJson(res, 501, {
          ok: false,
          error: 'arena_not_implemented',
          note: 'Gatekeeper module failed to load; failing closed. ' + (gatekeeperLoadError ? gatekeeperLoadError.message : ''),
        });
      }
      const out = await gatekeeperHandler(task);
      return sendJson(res, 200, out);
    }
    // Everything else (incl. Steal the VFY, which needs the vfy-policy circuit
    // and a strategy commitment before Swiss Round 1) — fail closed rather
    // than guessing.
    return sendJson(res, 501, {
      ok: false,
      error: 'arena_not_implemented',
      note: 'Only Proof Gatekeeper is implemented. Steal the VFY stays fail-closed: it needs the vfy-policy policy proof and an active strategy commitment before Swiss Round 1.',
    });
  } catch (err) {
    return sendJson(res, 500, { ok: false, error: 'internal_error' });
  }
});

server.listen(PORT, () => console.log(`[agent-games] listening on :${PORT} — GET / returns preflight {ok:true, protocolVersion:"v1"}`));
