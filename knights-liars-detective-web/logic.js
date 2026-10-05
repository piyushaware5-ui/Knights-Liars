/* logic.js - expression trees, evaluation, text/formula rendering, solver, generator */
const V=i=>({t:'var',i}),N=a=>({t:'not',a}),AND=o=>({t:'and',o}),OR=o=>({t:'or',o}),XOR=(l,r)=>({t:'xor',l,r}),IMP=(l,r)=>({t:'imp',l,r}),IFF=(l,r)=>({t:'iff',l,r}),ONE=o=>({t:'one',o});
function ev(e,a){switch(e.t){case'var':return a[e.i];case'not':return !ev(e.a,a);case'and':return e.o.every(x=>ev(x,a));case'or':return e.o.some(x=>ev(x,a));case'xor':return ev(e.l,a)!==ev(e.r,a);case'imp':return !ev(e.l,a)||ev(e.r,a);case'iff':return ev(e.l,a)===ev(e.r,a);case'one':return e.o.filter(x=>ev(x,a)).length===1}}
/* negation with De Morgan */
function neg(e){switch(e.t){case'not':return e.a;case'and':return OR(e.o.map(neg));case'or':return AND(e.o.map(neg));case'imp':return AND([e.l,neg(e.r)]);case'iff':return XOR(e.l,e.r);case'xor':return IFF(e.l,e.r);default:return N(e)}}
const KINDS={knight:['X is a Knight',1],liar:['X is a Liar',1],same:['X and Y are the same type',2],different:['X and Y are different types',2],implies:['If X is a Knight then Y is a Knight',2],alo_liar:['At least one of the group is a Liar','g'],alo_knight:['At least one of the group is a Knight','g'],one_knight:['Exactly one of the group is a Knight','g'],all_knights:['All of the group are Knights','g'],all_liars:['All of the group are Liars','g']};
function mk(k,t){if(KINDS[k][1]==='g')t=[...new Set(t)];const v=t.map(V);switch(k){case'knight':return v[0];case'liar':return N(v[0]);case'same':return IFF(v[0],v[1]);case'different':return XOR(v[0],v[1]);case'implies':return IMP(v[0],v[1]);case'alo_liar':return OR(t.map(i=>N(V(i))));case'alo_knight':return OR(v);case'one_knight':return ONE(v);case'all_knights':return AND(v);case'all_liars':return AND(t.map(i=>N(V(i))))}}
function cmb(o,a,b){return o==='and'?AND([a,b]):o==='or'?OR([a,b]):o==='xor'?XOR(a,b):IMP(a,b)}
const names=n=>Array.from({length:n},(_,i)=>String.fromCharCode(65+i));
/* natural language */
const isV=e=>e.t==='var',isNV=e=>e.t==='not'&&e.a.t==='var',isAt=e=>isV(e)||isNV(e),ix=o=>o.map(x=>isV(x)?x.i:x.a.i);
const grp=(ix,nm)=>[...new Set(ix)].sort((a,b)=>a-b).join()===nm.map((_,i)=>i).join()?'us':ix.map(i=>nm[i]).join(', ');
function tx(e,nm){const I=x=>{const s=tx(x,nm);return isAt(x)?s:'('+s+')'};switch(e.t){
case'var':return nm[e.i]+' is a Knight';
case'not':return isV(e.a)?nm[e.a.i]+' is a Liar':'It is not the case that '+I(e.a);
case'iff':return isV(e.l)&&isV(e.r)?`${nm[e.l.i]} and ${nm[e.r.i]} are the same type`:`${I(e.l)} if and only if ${I(e.r)}`;
case'xor':return isV(e.l)&&isV(e.r)?`${nm[e.l.i]} and ${nm[e.r.i]} are different types`:`Either ${I(e.l)} or ${I(e.r)}, but not both`;
case'imp':return `If ${I(e.l)} then ${I(e.r)}`;
case'one':return e.o.every(isV)?`Exactly one of ${grp(ix(e.o),nm)} is a Knight`:'Exactly one of the following is true: '+e.o.map(I).join('; ');
case'or':return e.o.every(isV)?`At least one of ${grp(ix(e.o),nm)} is a Knight`:e.o.every(isNV)?`At least one of ${grp(ix(e.o),nm)} is a Liar`:e.o.map(I).join(' or ');
case'and':return e.o.every(isV)?`All of ${grp(ix(e.o),nm)} are Knights`:e.o.every(isNV)?`All of ${grp(ix(e.o),nm)} are Liars`:e.o.map(I).join(' and ')}}
const text=(e,nm)=>{const s=tx(e,nm);return s[0].toUpperCase()+s.slice(1)};
/* logical notation */
function fm(e,nm,top){switch(e.t){
case'var':return 'K_'+nm[e.i];
case'not':return '¬'+(e.a.t==='var'||e.a.t==='not'?fm(e.a,nm,0):'('+fm(e.a,nm,1)+')');
case'one':return 'Exactly1('+e.o.map(x=>fm(x,nm,1)).join(', ')+')';
default:{let s;if(e.t==='and'||e.t==='or'){if(e.o.length===1)return fm(e.o[0],nm,top);s=e.o.map(x=>fm(x,nm,0)).join(e.t==='and'?' ∧ ':' ∨ ')}else s=fm(e.l,nm,0)+(e.t==='imp'?' → ':e.t==='xor'?' ⊕ ':' ↔ ')+fm(e.r,nm,0);return top?s:'('+s+')'}}}
const cons=(i,e,nm)=>'K_'+nm[i]+' ↔ '+fm(e,nm,0);
/* solver: full truth table, K_i <-> S_i */
function asg(n){const r=[];for(let k=0;k<(1<<n);k++)r.push(Array.from({length:n},(_,i)=>!((k>>(n-1-i))&1)));return r}
function analyze(st){return asg(st.length).map(a=>{const s=st.map(e=>ev(e,a)),c=a.map((v,i)=>v===s[i]);return{a,s,c,ok:c.every(Boolean)}})}
const solve=st=>analyze(st).filter(r=>r.ok).map(r=>r.a);
const role=b=>b?'Knight':'Liar',TF=b=>b?'T':'F',fa=(a,nm)=>'('+a.map((v,i)=>nm[i]+'='+role(v)).join(', ')+')';
const fails=r=>r.c.map((ok,i)=>ok?-1:i).filter(i=>i>=0);
const fshort=(r,i,nm)=>`${nm[i]}: K_${nm[i]}=${TF(r.a[i])} but S_${nm[i]}=${TF(r.s[i])}`;
const flong=(r,i,nm)=>r.a[i]?`${nm[i]} is a Knight, so their statement must be true, but it is false`:`${nm[i]} is a Liar, so their statement must be false, but it is true`;
function caseAn(st,nm,p){const rows=analyze(st),L=[],sv={};
[true,false].forEach((h,k)=>{L.push(`<p><b>Case ${k+1}: assume ${nm[p]} is a ${role(h)}.</b></p>`);
L.push('<p>'+(h?`${nm[p]} tells the truth, so this must hold: “${text(st[p],nm)}”.`:`${nm[p]} lies, so the statement is false. By negation / De Morgan's laws this means: “${text(neg(st[p]),nm)}”.`)+'</p>');
const cr=rows.filter(r=>r.a[p]===h),ok=cr.filter(r=>r.ok);sv[h]=ok.length;
L.push('<ul>'+cr.map(r=>`<li>${fa(r.a,nm)} → `+(r.ok?'consistent ✅':'✗ '+flong(r,fails(r)[0],nm))+'</li>').join('')+'</ul>');
L.push(ok.length?`<p>${ok.length} consistent completion(s) survive, so this case is possible.</p>`:'<p>Every completion contradicts some statement, so this case is impossible (proof by contradiction).</p>')});
const t=sv[true]+sv[false],P=nm[p];
L.push('<p><b>Conclusion:</b> '+(t===0?'both cases are impossible, so the statements are contradictory and no valid assignment exists.':!sv[true]?`${P} cannot be a Knight, so ${P} is a Liar.`:!sv[false]?`${P} cannot be a Liar, so ${P} is a Knight.`:`both cases survive, so ${P}'s type is not determined (${t} solutions in total).`)+'</p>');return L}
function mkHint(st,nm,rev){const rows=analyze(st),sols=rows.filter(r=>r.ok).map(r=>r.a);if(!sols.length)return null;
for(let i=0;i<st.length;i++){if(rev.includes(i))continue;const v=sols.map(s=>s[i]);if(!v.every(x=>x===v[0]))continue;
const o=!v[0],bad=rows.filter(r=>r.a[i]===o),L=[`Suppose ${nm[i]} were a ${role(o)}. Check the possible worlds:`,...bad.slice(0,3).map(r=>`${fa(r.a,nm)} fails: ${flong(r,fails(r)[0],nm)}.`)];
if(bad.length>3)L.push(`…and the other ${bad.length-3} world(s) fail in the same way.`);
L.push(`Every world with ${nm[i]} as a ${role(o)} is contradictory, so ${nm[i]} must be a ${role(v[0])}.`);return{p:i,k:v[0],L}}return null}
/* generator: random hidden world -> consistent statements -> keep only if exactly 1 solution */
const LV={Easy:2,Medium:3,Hard:4,Expert:5},ORD=Object.keys(LV),EK=['knight','liar','same','different'],MK=[...EK,'implies','alo_liar','alo_knight','one_knight'];
const rnd=n=>Math.floor(Math.random()*n),ch=a=>a[rnd(a.length)];
function sample(n,k){const a=[...Array(n).keys()];for(let i=n-1;i>0;i--){const j=rnd(i+1);[a[i],a[j]]=[a[j],a[i]]}return a.slice(0,k)}
function ga(sp,n,ks){const k=ch(ks),ar=KINDS[k][1];const t=ar===1?[ch([...Array(n).keys()].filter(j=>j!==sp))]:ar===2?sample(n,2):sample(n,2+rnd(n-1)).sort((a,b)=>a-b);return mk(k,t)}
function rs(sp,n,l){if((l==='Hard'||l==='Expert')&&Math.random()<.4)return cmb(ch(['and','or','implies','xor']),ga(sp,n,MK),ga(sp,n,MK));return ga(sp,n,l==='Easy'?EK:MK)}
function gen(level){const n=LV[level];for(let it=0;it<50000;it++){const h=Array.from({length:n},()=>Math.random()<.5),st=[];let ok=true;
for(let i=0;i<n&&ok;i++){let s=null;for(let t=0;t<100;t++){const c=rs(i,n,level);if(ev(c,h)===h[i]){s=c;break}}if(s)st.push(s);else ok=false}
if(!ok)continue;const so=solve(st);if(so.length===1)return{level,n,st,sol:so[0]}}throw Error('generation failed')}
