/* app.js - UI (plain JS, no libraries; works from file://) */
const $=id=>document.getElementById(id);
const S={mode:'play',score:0,streak:0,best:0,unl:1,cbl:{Easy:0,Medium:0,Hard:0,Expert:0},level:'Easy',puz:null,pid:0,guess:[],ans:false,res:null,hints:[],split:0,note:''};
const PTS={Easy:10,Medium:20,Hard:30,Expert:50},HC=5,UN=3;let showF=true;
const C={n:3,split:0,p:[]};
const defPart=i=>({k:'knight',x:(i+1)%3,y:(i+2)%3,g:[1,1,1,1,1,1]});
for(let i=0;i<6;i++)C.p.push({a:defPart(i),op:'',b:defPart(i),neg:false});
function setMode(m){S.mode=m;draw()}
function newP(){S.puz=gen(S.level);S.pid++;S.guess=Array(S.puz.n).fill(null);S.ans=false;S.res=null;S.hints=[];S.split=0;S.note='';draw()}
function setLevel(l){S.level=l;newP()}
function setG(i,v){if(!S.ans){S.guess[i]=v;draw()}}
function submit(){if(S.ans)return;if(S.guess.some(g=>g===null)){S.note='Choose Knight or Liar for every suspect first.';return draw()}
const p=S.puz,g=S.guess,ok=g.every((v,i)=>v===p.sol[i]);let gain=0,unl=null;
if(ok){gain=Math.max(0,PTS[p.level]-HC*S.hints.length);S.score+=gain;S.streak++;S.best=Math.max(S.best,S.streak);S.cbl[p.level]++;
const ix=ORD.indexOf(p.level);if(S.cbl[p.level]>=UN&&ix+1===S.unl&&S.unl<ORD.length){S.unl++;unl=ORD[S.unl-1]}}else S.streak=0;
S.ans=true;S.res={g,ok,gain,unl};S.note='';draw()}
function hint(){const p=S.puz,h=mkHint(p.st,names(p.n),S.hints.map(x=>x.p));if(h){S.hints.push(h);S.note=''}else S.note='No more suspects can be revealed with a hint.';draw()}
function stmts(st,nm){return `<label><input type=checkbox ${showF?'checked':''} onchange="showF=this.checked;draw()"> Show logical notation</label><div class=cards>`+st.map((e,i)=>`<div class=card><b>${nm[i]}</b> says: “${text(e,nm)}”${showF?`<div class=f>S_${nm[i]} = ${fm(e,nm,1)}<br>${cons(i,e,nm)}</div>`:''}</div>`).join('')+'</div>'}
function expl(st,nm,guess,split,ref){const rows=analyze(st);
let h='<h3>Step 1 – The truth table</h3><p class=m>Each row is one possible world (Knight = T, Liar = F). A row survives only if K_i ↔ S_i holds for every suspect.</p><div class=sc><table><tr>'+nm.map(x=>`<th>K_${x}</th>`).join('')+nm.map(x=>`<th>S_${x}</th>`).join('')+nm.map(x=>`<th>K_${x} ↔ S_${x}</th>`).join('')+'<th>All consistent?</th><th>Reason</th>'+(guess?'<th>Your guess</th>':'')+'</tr>';
rows.forEach(r=>{h+=`<tr class=${r.ok?'ok':'no'}>`+r.a.map(v=>`<td>${TF(v)}</td>`).join('')+r.s.map(v=>`<td>${TF(v)}</td>`).join('')+r.c.map(v=>`<td>${TF(v)}</td>`).join('')+`<td>${r.ok?'✅ Yes':'❌ No'}</td><td class=l>${r.ok?'Survives: every K_i ↔ S_i holds':fails(r).map(i=>fshort(r,i,nm)).join('; ')}</td>`+(guess?`<td>${r.a.every((v,i)=>v===guess[i])?'◀ your guess':''}</td>`:'')+'</tr>'});
h+='</table></div><p class=m>🟩 green = surviving row (solution) · 🟥 red = eliminated row, with the reason.</p><h3>Step 2 – Case analysis</h3>Split the cases on suspect <select onchange="'+ref+'=+this.value;draw()">'+nm.map((x,i)=>`<option value=${i} ${i===split?'selected':''}>${x}</option>`).join('')+'</select>'+caseAn(st,nm,split).join('');return h}
function playHTML(){const p=S.puz,nm=names(p.n);let h='<div class=row>'+ORD.map((l,i)=>i<S.unl?`<button class="${l===S.level?'on':''}" onclick="setLevel('${l}')">${l} (${LV[l]}) ${Math.min(S.cbl[l],UN)}/${UN}</button>`:`<button disabled>🔒 ${l}</button>`).join('')+'<button class=pri onclick="newP()">New Puzzle</button></div><p class=m>Solve 3 puzzles at your top level to unlock the next one.</p>';
if(S.note)h+=`<div class="box warn">${S.note}</div>`;
h+=`<h2>Case #${S.pid} · ${p.level} · ${p.n} suspects</h2>`+stmts(p.st,nm)+'<h3>Your verdict</h3><div class=row>'+nm.map((x,i)=>`<div class=sus><b>${x}</b><button class="${S.guess[i]===true?'on':''}" ${S.ans?'disabled':''} onclick="setG(${i},true)">Knight</button><button class="${S.guess[i]===false?'on':''}" ${S.ans?'disabled':''} onclick="setG(${i},false)">Liar</button></div>`).join('')+'</div>';
h+=`<div class=row><button class=pri ${S.ans?'disabled':''} onclick="submit()">Submit</button><button class=hint ${S.ans?'disabled':''} onclick="hint()">Hint (−${HC} pts)</button><span>Reward if correct: <b>${Math.max(0,PTS[p.level]-HC*S.hints.length)}</b> pts</span></div>`;
S.hints.forEach(x=>{h+=`<div class="box info">💡 Hint: <b>${nm[x.p]}</b> is a <b>${role(x.k)}</b>.<details><summary>Why? (proof by contradiction)</summary>${x.L.map(l=>'<div>'+l+'</div>').join('')}</details></div>`});
if(S.ans){const r=S.res;if(r.ok)h+=`<div class="box good">✅ Correct! +${r.gain} points.${r.unl?` 🔓 New level unlocked: ${r.unl}!`:''}</div>`;
else{const row=analyze(p.st).find(x=>x.a.every((v,i)=>v===r.g[i]));h+=`<div class="box bad">❌ Wrong. The unique solution is ${fa(p.sol,nm)}.<br>Why your answer ${fa(r.g,nm)} fails:<ul>${fails(row).map(i=>`<li>${flong(row,i,nm)}.</li>`).join('')}</ul></div>`}
h+=expl(p.st,nm,r.g,S.split,'S.split')}return h}
/* ---- custom mode ---- */
function cs(i,pt,f,v){C.p[i][pt][f]=v;draw()}
function cg(i,pt,j,c){C.p[i][pt].g[j]=c?1:0;draw()}
function part(i,pt,c,n,nm){const ar=KINDS[c.k][1],sel=f=>`<select onchange="cs(${i},'${pt}','${f}',+this.value)">`+nm.map((x,j)=>`<option value=${j} ${Math.min(c[f],n-1)===j?'selected':''}>${x}</option>`).join('')+'</select> ';
return `<select onchange="cs(${i},'${pt}','k',this.value)">`+Object.keys(KINDS).map(k=>`<option value=${k} ${k===c.k?'selected':''}>${KINDS[k][0]}</option>`).join('')+'</select> '+(ar===1?'X '+sel('x'):ar===2?'X '+sel('x')+'Y '+sel('y'):'Group: '+nm.map((x,j)=>`<label><input type=checkbox ${c.g[j]?'checked':''} onchange="cg(${i},'${pt}',${j},this.checked)">${x}</label>`).join(''))}
function build(c,n){const s=q=>{const ar=KINDS[q.k][1];if(ar===1)return mk(q.k,[Math.min(q.x,n-1)]);if(ar===2)return mk(q.k,[Math.min(q.x,n-1),Math.min(q.y,n-1)]);const t=[...Array(n).keys()].filter(j=>q.g[j]);return t.length?mk(q.k,t):null};
let e=s(c.a);if(!e)return null;if(c.op){const b=s(c.b);if(!b)return null;e=cmb(c.op,e,b)}return c.neg?N(e):e}
function customHTML(){const n=C.n,nm=names(n),st=[];let h='<h2>Custom puzzle</h2><p class=m>Build each suspect\'s statement. The solver reports a contradiction, a unique solution, or multiple solutions.</p><div class=row>Number of suspects: <select onchange="C.n=+this.value;draw()">'+[1,2,3,4,5,6].map(k=>`<option ${k===n?'selected':''}>${k}</option>`).join('')+'</select></div>';let bad=false;
for(let i=0;i<n;i++){const c=C.p[i];h+=`<div class=card><b>${nm[i]} says:</b><div class=row>${part(i,'a',c.a,n,nm)}</div><div class=row>Combine with second statement: <select onchange="C.p[${i}].op=this.value;draw()">`+[['','(none)'],['and','AND'],['or','OR'],['xor','XOR (exactly one)'],['implies','IF … THEN']].map(o=>`<option value="${o[0]}" ${c.op===o[0]?'selected':''}>${o[1]}</option>`).join('')+'</select></div>'+(c.op?`<div class=row>${part(i,'b',c.b,n,nm)}</div>`:'')+`<label><input type=checkbox ${c.neg?'checked':''} onchange="C.p[${i}].neg=this.checked;draw()"> Negate the whole statement (NOT)</label></div>`;
const e=build(c,n);if(e)st.push(e);else bad=true}
if(bad)return h+'<div class="box warn">Pick at least one suspect for every group statement.</div>';
h+='<h3>Your puzzle</h3>'+stmts(st,nm)+'<h3>Solver result</h3>';const so=solve(st);
h+=so.length===0?'<div class="box bad">⚠️ Contradiction – no assignment of Knights and Liars satisfies all statements.</div>':so.length===1?`<div class="box good">✅ Unique solution: ${fa(so[0],nm)}</div>`:`<div class="box warn">🔀 ${so.length} solutions – the statements do not determine everyone:<ul>${so.map(a=>'<li>'+fa(a,nm)+'</li>').join('')}</ul></div>`;
return h+expl(st,nm,null,Math.min(C.split,n-1),'C.split')}
function draw(){$('tp').className=S.mode==='play'?'on':'';$('tc').className=S.mode==='custom'?'on':'';
$('stats').innerHTML=`Score <b>${S.score}</b> · Streak <b>${S.streak}</b> · Best <b>${S.best}</b>`;
$('app').innerHTML=S.mode==='play'?playHTML():customHTML()}
newP();
