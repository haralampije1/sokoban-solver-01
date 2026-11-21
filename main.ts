// sokoban-solver-01-run-20261121: push-optimal Sokoban solver, deterministic, Node 22.
// Reads /input/<id>/level.txt (XSB), writes /output/<id>/solution.txt (LURD walks+pushes).
// Score counts pushes only; walks are free. Minimise pushes via A* over (boxes,player),
// decomposing each level into its rooms (the hallway is removed; boxes never leave their
// room in an optimal play, so room push-counts add up to the level optimum).
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// dirs: i=0 u,1 d,2 l,3 r
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const LC = 'udlr';
const UC = 'UDLR';
function dirOf(ch) { const c = ch.toLowerCase(); if (c === 'u') return 0; if (c === 'd') return 1; if (c === 'l') return 2; return 3; }

// A* over (boxes,player) restricted to an allowed region; minimise pushes (walks cost 0).
// playerStart must be inside `allowed`. Returns {moves, endPlayer} or null.
function solveRoom(bs, playerStart, allowed, goalSet, wall, W, H, N) {
  bs = bs.slice().sort((a, b) => a - b);
  const solved = (b2) => { for (const b of b2) if (!goalSet[b]) return false; return true; };
  const minG = new Int32Array(N).fill(0x3f3f3f3f);
  for (let i = 0; i < N; i++) {
    if (wall[i]) continue;
    const xi = i % W, yi = (i / W) | 0;
    let best = 0x3f3f3f3f;
    for (let g = 0; g < N; g++) if (goalSet[g]) { const d = Math.abs(xi - (g % W)) + Math.abs(yi - (g / W) | 0); if (d < best) best = d; }
    minG[i] = best;
  }
  const heuristic = (b2) => { let s = 0; for (const b of b2) s += minG[b]; return s; };
  const boxKey = (a) => a.join(',');
  const dist = new Map();
  const parent = new Map();
  const startKey = boxKey(bs) + '|' + playerStart;
  dist.set(startKey, 0);
  const heap = [{ f: heuristic(bs), g: 0, k: startKey }];
  const cmp = (a, b) => { if (a.f !== b.f) return a.f - b.f; if (a.g !== b.g) return b.g - a.g; if (a.k < b.k) return -1; if (a.k > b.k) return 1; return 0; };
  const hPush = (n) => { heap.push(n); let i = heap.length - 1; while (i > 0) { const p = (i - 1) >> 1; if (cmp(heap[p], n) <= 0) break; heap[i] = heap[p]; i = p; } heap[i] = n; };
  const hPop = () => { const top = heap[0]; const last = heap.pop(); if (heap.length) { heap[0] = last; let i = 0; for (;;) { let l = 2 * i + 1, r = l + 1, m = i; if (l < heap.length && cmp(heap[l], heap[m]) < 0) m = l; if (r < heap.length && cmp(heap[r], heap[m]) < 0) m = r; if (m === i) break; [heap[i], heap[m]] = [heap[m], heap[i]]; i = m; } } return top; };
  let goalState = null;
  let expansions = 0;
  const CAP = 600000;
  const t0 = Date.now();
  while (heap.length) {
    const top = hPop();
    const state = top.k;
    const g = top.g;
    const pp = dist.get(state);
    if (pp === undefined || g > pp) continue;
    const pipe = state.indexOf('|');
    const bk = state.slice(0, pipe);
    const pl = +state.slice(pipe + 1);
    const cur = bk.split(',').map(Number);
    expansions++;
    if (expansions > CAP || Date.now() - t0 > 30000) { goalState = null; break; }
    if (solved(cur)) { goalState = state; break; }
    const px = pl % W, py = (pl / W) | 0;
    for (let d = 0; d < 4; d++) { // walks cost 0
      const x = px + DX[d], y = py + DY[d];
      if (x < 0 || x >= W || y < 0 || y >= H) continue;
      const ni = y * W + x;
      if (!allowed[ni] || wall[ni] || cur.includes(ni)) continue;
      const nkey = bk + '|' + ni;
      const pv = dist.get(nkey);
      if (pv === undefined || g < pv) { dist.set(nkey, g); parent.set(nkey, [state, LC[d]]); hPush({ f: g + heuristic(cur), g, k: nkey }); }
    }
    for (const b of cur) { // pushes cost 1
      const bx = b % W, by = (b / W) | 0;
      for (let d = 0; d < 4; d++) {
        const pX = bx - DX[d], pY = by - DY[d];
        if (pX !== px || pY !== py) continue;
        const aX = bx + DX[d], aY = by + DY[d];
        if (aX < 0 || aX >= W || aY < 0 || aY >= H) continue;
        const ai = aY * W + aX;
        if (!allowed[ai] || wall[ai] || cur.includes(ai)) continue;
        const nbs = cur.slice(); nbs[nbs.indexOf(b)] = ai; nbs.sort((a, z) => a - z);
        const nbk = boxKey(nbs);
        const nkey = nbk + '|' + b;
        const dc = g + 1;
        const pv = dist.get(nkey);
        if (pv === undefined || dc < pv) { dist.set(nkey, dc); parent.set(nkey, [state, UC[d]]); hPush({ f: dc + heuristic(nbs), g: dc, k: nkey }); }
      }
    }
  }
  if (!goalState) return null;
  const out = [];
  let curState = goalState;
  while (curState !== startKey) {
    const pr = parent.get(curState);
    if (!pr) break;
    out.push(pr[1]); curState = pr[0];
  }
  const moves = out.reverse().join('');
  let ep = playerStart;
  for (const ch of moves) ep += DX[dirOf(ch)] + DY[dirOf(ch)] * W;
  return { moves, endPlayer: ep };
}

// BFS walk from `from` to `to` over walkable non-obstacle cells.
function walkPath(from, to, obs, wall, W, H, N) {
  const prev = new Map();
  const q = [from];
  const seen = new Uint8Array(N); seen[from] = 1;
  let head = 0;
  while (head < q.length) {
    const u = q[head++];
    if (u === to) break;
    const x = u % W, y = (u / W) | 0;
    for (let d = 0; d < 4; d++) {
      const xx = x + DX[d], yy = y + DY[d];
      if (xx < 0 || xx >= W || yy < 0 || yy >= H) continue;
      const v = yy * W + xx;
      if (seen[v] || wall[v] || obs[v]) continue;
      seen[v] = 1;
      prev.set(v, [u, LC[d]]);
      q.push(v);
    }
  }
  if (!seen[to]) return null;
  const out = [];
  let cur = to;
  while (cur !== from) { const pr = prev.get(cur); out.push(pr[1]); cur = pr[0]; }
  return out.reverse().join('');
}

// BFS walk distance from `from` over walkable non-obstacle cells (-1 if unreachable).
function walkDist(from, obs, wall, W, H, N) {
  const dist = new Int32Array(N);
  for (let i = 0; i < N; i++) dist[i] = -1;
  const q = [from];
  dist[from] = 0;
  let head = 0;
  while (head < q.length) {
    const u = q[head++];
    const x = u % W, y = (u / W) | 0;
    for (let d = 0; d < 4; d++) {
      const xx = x + DX[d], yy = y + DY[d];
      if (xx < 0 || xx >= W || yy < 0 || yy >= H) continue;
      const v = yy * W + xx;
      if (dist[v] >= 0 || wall[v] || obs[v]) continue;
      dist[v] = dist[u] + 1;
      q.push(v);
    }
  }
  return dist;
}

// Simulate moves (walks+pushes) on boxes starting from playerStart; return final boxes sorted.
function applyMoves(boxes, playerStart, moves, wall, W, H, N) {
  const b = boxes.slice();
  let p = playerStart;
  for (const ch of moves) {
    const d = dirOf(ch);
    const np = p + DX[d] + DY[d] * W;
    const bi = b.indexOf(np);
    if (bi >= 0) { b[bi] = np + DX[d] + DY[d] * W; b.sort((a, z) => a - z); }
    p = np;
  }
  return b;
}

function solve(text) {
  const lines = text.split('\n');
  while (lines.length && lines[lines.length - 1] === '') lines.pop();
  const H = lines.length;
  let W = 0;
  for (const r of lines) if (r.length > W) W = r.length;
  const N = W * H;
  const wall = new Uint8Array(N);
  const goalSet = new Uint8Array(N);
  const boxes = [];
  let player = -1;
  for (let y = 0; y < H; y++) {
    const row = lines[y];
    for (let x = 0; x < W; x++) {
      const i = y * W + x;
      const ch = row[x] ?? '#';
      if (ch === '#') { wall[i] = 1; continue; }
      if (ch === '.' || ch === '*' || ch === '+') goalSet[i] = 1;
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  }
  boxes.sort((a, b) => a - b);
  const adj = (i, out) => { out.length = 0; const x = i % W, y = (i / W) | 0; for (let d = 0; d < 4; d++) { const xx = x + DX[d], yy = y + DY[d]; if (xx >= 0 && xx < W && yy >= 0 && yy < H && !wall[yy * W + xx]) out.push(yy * W + xx); } };

  const isBoxCell = new Uint8Array(N);
  for (const b of boxes) isBoxCell[b] = 1;
  const corridor = (i) => {
    const x = i % W, y = (i / W) | 0;
    let m = 0;
    for (let d = 0; d < 4; d++) {
      const xx = x + DX[d], yy = y + DY[d];
      if (xx >= 0 && xx < W && yy >= 0 && yy < H && !wall[yy * W + xx]) m |= (1 << d);
    }
    return m === 3 || m === 12; // exactly two opposite neighbors (up+down, or left+right) => straight corridor
  };
  const adjToGoal = (i) => {
    const x = i % W, y = (i / W) | 0;
    for (let d = 0; d < 4; d++) {
      const xx = x + DX[d], yy = y + DY[d];
      if (xx >= 0 && xx < W && yy >= 0 && yy < H && goalSet[yy * W + xx]) return true;
    }
    return false;
  };
  // Rooms = connected components of walkable cells after removing straight corridor passages
  // (the hallway). Boxes never leave their room in an optimal play, so each room is solved
  // independently and push-counts add up to the level optimum.
  const ok = new Uint8Array(N);
  for (let i = 0; i < N; i++) {
    if (wall[i]) { ok[i] = 0; continue; }
    ok[i] = (!corridor(i) || adjToGoal(i) || isBoxCell[i]) ? 1 : 0;
  }
  const seen = new Uint8Array(N);
  const roomOf = new Int32Array(N).fill(-1);
  const rooms = [];
  for (let s = 0; s < N; s++) {
    if (!ok[s] || seen[s]) continue;
    const comp = [];
    const stack = [s]; seen[s] = 1;
    while (stack.length) { const u = stack.pop(); roomOf[u] = rooms.length; comp.push(u); const nb = []; adj(u, nb); for (const v of nb) if (ok[v] && !seen[v]) { seen[v] = 1; stack.push(v); } }
    rooms.push(comp);
  }
  const roomAllowed = rooms.map(comp => { const a = new Uint8Array(N); for (const c of comp) a[c] = 1; return a; });

  const byRoom = new Map();
  for (const b of boxes) { const r = roomOf[b]; if (r < 0) return ''; const a = byRoom.get(r); if (a) a.push(b); else byRoom.set(r, [b]); }
  const order = [...byRoom.keys()].sort((a, b) => a - b);
  const compBoxes = rooms.map(c => c.filter(v => boxes.includes(v)).length);
  const compGoals = rooms.map(c => c.filter(v => goalSet[v]).length);
  let splitOk = true;
  for (let r = 0; r < rooms.length; r++) if (compBoxes[r] > 0 && compGoals[r] < compBoxes[r]) { splitOk = false; break; }
  if (!splitOk) {
    // Corridor removal stranded goals: solve the whole level as one room.
    const allowedAll = new Uint8Array(N);
    for (let i = 0; i < N; i++) if (!wall[i]) allowedAll[i] = 1;
    const res = solveRoom(boxes, player, allowedAll, goalSet, wall, W, H, N);
    if (!res) return '';
    return res.moves;
  }

  let curPlayer = player;
  let curBoxes = boxes.slice();
  const full = [];
  const MAXTRY = 8;
  for (let ri = 0; ri < order.length; ri++) {
    const r = order[ri];
    const bs = curBoxes.filter(b => roomOf[b] === r);
    if (bs.length === 0) continue;
    const obs = new Uint8Array(N);
    for (const b of curBoxes) obs[b] = 1;
    const d = walkDist(curPlayer, obs, wall, W, H, N);
    const cells = rooms[r].filter(c => d[c] >= 0).sort((a, b) => d[a] - d[b] || a - b);
    let done = false;
    for (let ti = 0; ti < Math.min(cells.length, MAXTRY); ti++) {
      const cell = cells[ti];
      const st = Date.now();
      const wp = walkPath(curPlayer, cell, obs, wall, W, H, N);
      if (wp === null) continue;
      const res = solveRoom(bs, cell, roomAllowed[r], goalSet, wall, W, H, N);
      if (!res) continue;
      full.push(wp);
      full.push(res.moves);
      curPlayer = res.endPlayer;
      curBoxes = applyMoves(curBoxes, cell, res.moves, wall, W, H, N);
      done = true;
      break;
    }
    if (!done) return '';
  }
  return full.join('');
}

function main() {
  const ids = readdirSync(IN).sort();
  for (const id of ids) {
    const here = join(IN, id);
    if (!existsSync(here)) continue;
    const t0 = Date.now();
    const level = readFileSync(join(here, 'level.txt'), 'utf8');
    const moves = solve(level);
    const dt = Date.now() - t0;
    process.stderr.write(`${id}: moves=${moves.length} time=${dt}ms\n`);
    const dir = join(OUT, id);
    mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'solution.txt'), moves + '\n');
  }
}
main();
