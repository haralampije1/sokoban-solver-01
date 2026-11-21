import{readFileSync as R,readdirSync as S,writeFileSync as wt,mkdirSync as M}from'node:fs';import{join as j}from'node:path';import * as fs from 'node:fs';

const IN = process.env.MAKEFUN_INPUT_DIR;
const OUT = process.env.MAKEFUN_OUTPUT_DIR;

const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const LC = 'udlr';
const UC = 'UDLR';
function dirOf(c){const k=c.toLowerCase();return k==='u'?0:k==='d'?1:k==='l'?2:3;}

function walkDist(from, obs, wall, W, H, N){
  const dist = new Int32Array(N); for(let i=0;i<N;i++)dist[i]=-1;
  const q=[from]; dist[from]=0; let hd=0;
  while(hd<q.length){
    const u=q[hd++], x=u%W, y=u/W|0;
    for(let d=0;d<4;d++){
      const v=(y+DY[d])*W+(x+DX[d]);
      if(v<0||v>=N||dist[v]>=0||wall[v]||obs[v])continue;
      dist[v]=dist[u]+1; q.push(v);
    }
  }
  return dist;
}
function walkPath(from,to,obs,wall,W,H,N){
  const prev=new Uint8Array(N).fill(255), prevd=new Uint8Array(N);
  const q=[from]; prev[from]=from;
  let hd=0;
  while(hd<q.length){
    const u=q[hd++]; if(u===to)break;
    const x=u%W, y=u/W|0;
    for(let d=0;d<4;d++){
      const v=(y+DY[d])*W+(x+DX[d]);
      if(v<0||v>=N||prev[v]!==255||wall[v]||obs[v])continue;
      prev[v]=u; prevd[v]=d; q.push(v);
    }
  }
  if(prev[to]===255)return null;
  const out=[]; let cur=to;
  while(cur!==from){out.push(LC[prevd[cur]]);cur=prev[cur];}
  return out.reverse().join('');
}

function solveRoom(bs0, pl, allowed, goal, wall, W, H, N){
  bs0=bs0.slice().sort((a,b)=>a-b);
  const solved=bs=>{for(const b of bs)if(!goal[b])return false;return true;};
  if(solved(bs0))return {moves:'',endPlayer:pl};
  const key=(bs,pl)=>bs.join(',')+'#'+pl;
  const dist=new Map([[key(bs0,pl),0]]);
  const par=new Map([[key(bs0,pl),null]]);
  let gk=null;
  let layer=[key(bs0,pl)];
  const t0=Date.now();
  while(layer.length&&!gk&&Date.now()-t0<20000){
    const nxt=[];
    for(const k of layer){
      const pi=k.indexOf('#'); const bs=k.slice(0,pi).split(',').map(Number); const p=+k.slice(pi+1);
      const cur=new Uint8Array(N); for(const b of bs)cur[b]=1;
      const reach=new Uint8Array(N); const rq=[p]; reach[p]=1; let ri=0;
      while(ri<rq.length){
        const u=rq[ri++], x=u%W, y=u/W|0;
        for(let d=0;d<4;d++){const v=(y+DY[d])*W+(x+DX[d]); if(v<0||v>=N||reach[v]||wall[v]||cur[v]||!allowed[v])continue; reach[v]=1; rq.push(v);}
      }
      for(const b of bs){
        const x=b%W, y=b/W|0;
        for(let d=0;d<4;d++){
          const ax=x+DX[d], ay=y+DY[d];
          if(ax<0||ax>=W||ay<0||ay>=H)continue;
          const ai=ay*W+ax;
          const pi2=(y-DY[d])*W+(x-DX[d]);
          if(pi2<0||pi2>=N||!reach[pi2])continue;
          if(wall[ai]||cur[ai])continue;
          if(!goal[ai]){const x2=ai%W,y2=ai/W|0; const u=y2-1<0||wall[ai-W], dn=y2+1>=H||wall[ai+W], lf=x2-1<0||wall[ai-1], rt=x2+1>=W||wall[ai+1]; if((u&&lf)||(u&&rt)||(dn&&lf)||(dn&&rt))continue;}
          const nbs=bs.slice(); nbs[nbs.indexOf(b)]=ai; nbs.sort((a,z)=>a-z);
          const nk=key(nbs,b);
          if(dist.has(nk))continue;
          const wp=walkPath(p,pi2,cur,wall,W,H,N);
          if(wp===null)continue;
          dist.set(nk,1); par.set(nk,[k,wp+UC[d]]);
          nxt.push(nk);
          if(solved(nbs)){gk=nk; break;}
        }
        if(gk)break;
      }
    }
    layer=nxt;
  }
  if(!gk)return null;
  const out=[]; let cur=gk;
  for(;;){const pr=par.get(cur); if(!pr)break; out.push(pr[1]); cur=pr[0];}
  const moves=out.reverse().join('');
  let ep=pl;
  for(const ch of moves) ep+=DX[dirOf(ch)]+DY[dirOf(ch)]*W;
  return {moves,endPlayer:ep};
}
function apply(boxes,pl,moves,wall,W,H,N){
  const b=boxes.slice(); let p=pl;
  for(const ch of moves){const d=dirOf(ch); const np=p+DX[d]+DY[d]*W; const bi=b.indexOf(np); if(bi>=0){b[bi]=np+DX[d]+DY[d]*W; b.sort((a,z)=>a-z);} p=np;}
  return b;
}
function solve(text){
  const lines=text.split('\n'); while(lines.length&&lines[lines.length-1]==='')lines.pop();
  const H=lines.length; let W=0; for(const r of lines) if(r.length>W)W=r.length;
  const N=W*H;
  const wall=new Uint8Array(N), goal=new Uint8Array(N);
  const boxes=[], isBox=new Uint8Array(N);
  let player=-1;
  for(let y=0;y<H;y++){const row=lines[y]||''; for(let x=0;x<W;x++){const i=y*W+x; const ch=row[x]; if(!ch||ch==='#'){wall[i]=1;continue;} if(ch==='.'||ch==='*'||ch==='+')goal[i]=1; if(ch==='$'||ch==='*'){boxes.push(i);isBox[i]=1;} if(ch==='@'||ch==='+')player=i;}}
  boxes.sort((a,b)=>a-b);
  const adj=(i,out)=>{out.length=0; const x=i%W, y=i/W|0; for(let d=0;d<4;d++){const xx=x+DX[d], yy=y+DY[d]; if(xx>=0&&xx<W&&yy>=0&&yy<H&&!wall[yy*W+xx])out.push(yy*W+xx);}};
  const corridor=i=>{const x=i%W, y=i/W|0; let m=0; for(let d=0;d<4;d++){const xx=x+DX[d], yy=y+DY[d]; if(xx>=0&&xx<W&&yy>=0&&yy<H&&!wall[yy*W+xx])m|=(1<<d);} return m===3||m===12;};
  const adjToGoal=i=>{const x=i%W, y=i/W|0; for(let d=0;d<4;d++){const xx=x+DX[d], yy=y+DY[d]; if(xx>=0&&xx<W&&yy>=0&&yy<H&&goal[yy*W+xx])return true;} return false;};
  const ok=new Uint8Array(N);
  for(let i=0;i<N;i++){if(wall[i])continue; ok[i]=(!corridor(i)||adjToGoal(i)||isBox[i])?1:0;}
  const seen=new Uint8Array(N); const roomOf=new Int32Array(N).fill(-1); const rooms=[];
  for(let s=0;s<N;s++){if(!ok[s]||seen[s])continue; const comp=[]; const stk=[s]; seen[s]=1; while(stk.length){const u=stk.pop(); roomOf[u]=rooms.length; comp.push(u); const nb=[]; adj(u,nb); for(const v of nb) if(ok[v]&&!seen[v]){seen[v]=1; stk.push(v);}} rooms.push(comp);}
  const roomAllowed=rooms.map(comp=>{const a=new Uint8Array(N); for(const c of comp)a[c]=1; return a;});
  const byRoom=new Map();
  for(const b of boxes){const r=roomOf[b]; if(r<0)return ''; const a=byRoom.get(r); if(a)a.push(b); else byRoom.set(r,[b]);}
  const order=[...byRoom.keys()].sort((a,b)=>a-b);
  let curPlayer=player, curBoxes=boxes.slice(), full=[];
  for(const r of order){
    const bs=curBoxes.filter(b=>roomOf[b]===r); if(bs.length===0)continue;
    const obs=new Uint8Array(N); for(const b of curBoxes)obs[b]=1;
    const d=walkDist(curPlayer,obs,wall,W,H,N);
    const cells=rooms[r].filter(c=>d[c]>=0).sort((a,b)=>d[a]-d[b]||a-b);
    let done=false;
    for(let ti=0;ti<cells.length;ti++){
      const cell=cells[ti], wp=walkPath(curPlayer,cell,obs,wall,W,H,N);
      if(wp===null)continue;
      const res=solveRoom(bs,cell,roomAllowed[r],goal,wall,W,H,N);
      if(!res)continue;
      full.push(wp); full.push(res.moves);
      curPlayer=res.endPlayer; curBoxes=apply(curBoxes,cell,res.moves,wall,W,H,N); done=true; break;
    }
    if(!done)return '';
  }
  return full.join('');
}

function main(){
  const ids=S(IN).sort();
  for(const id of ids){
    const here=IN+'/'+id; if(!fs.statSync(here).isDirectory())continue;
    const t0=Date.now();
    const level=R(here+'/level.txt','utf8');
    const moves=solve(level);
    const dt=Date.now()-t0;
    process.stderr.write(`${id}: moves=${moves.length} time=${dt}ms\n`);
    const dir=OUT+'/'+id; M(dir,{recursive:true});
    wt(dir+'/solution.txt',moves+'\n');
  }
}
main();
