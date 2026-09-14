(()=>{
const $=id=>document.getElementById(id);
const sec=$('map'),stage=$('mstage'),cv=$('mapc'),ctx=cv.getContext('2d');
const white=$('mwhite'),scaleEl=$('mscale'),coordEl=$('mcoord'),prof=$('mprof'),profSvg=$('mprofsvg');
const steps=[...document.querySelectorAll('.mstep')],stopRows=[...document.querySelectorAll('#mstops li')];
const params=new URLSearchParams(location.search),fM=parseFloat(params.get('m'));
const reduce=matchMedia('(prefers-reduced-motion: reduce)').matches;
const cl=(v,a=0,b=1)=>Math.min(b,Math.max(a,v)),sm=t=>t*t*(3-2*t),lerp=(a,b,t)=>a+(b-a)*t;
const ease=t=>t<.5?4*t*t*t:1-Math.pow(-2*t+2,3)/2;
let vw=0,vh=0,dpr=1,ready=0;
const KBR=[41.95,44.05,42.82,43.78,3000,1884],PKB=[43.56428,43.61125,43.43244,43.47369,2400,2902];
const proj=B=>(lat,lon)=>[(lon-B[0])/(B[1]-B[0])*B[4],(B[3]-lat)/(B[3]-B[2])*B[5]];
const toRep=proj(KBR),toPk=proj(PKB);
const mPerPx=B=>(B[1]-B[0])*Math.cos(43.3*Math.PI/180)*111000/B[4];
const repImg=new Image(),parkImg=new Image();
repImg.src='assets/map-kbr.webp';parkImg.src='assets/map-park.webp';
repImg.onload=parkImg.onload=()=>{ready++;kick()};
const PLACES=[
  {n:'Приэльбрусье',a:'≈2 400 м',lat:43.385,lon:42.585,side:'r'},
  {n:'Эльтюбю',a:'1 500 м',lat:43.269,lon:43.151,side:'l'},
  {n:'Чегемские водопады',a:'≈1 100 м',lat:43.416,lon:43.216,side:'r'},
  {n:'Церик-Кёль',a:'809 м',lat:43.234,lon:43.539,side:'r'},
  {n:'Язык Тролля',a:'≈2 600 м',lat:43.239,lon:43.310,side:'l'}
];
const ELBRUS={lat:43.3525,lon:42.4375},NALCHIK={lat:43.4565,lon:43.5875};
const repPts=PLACES.map(p=>toRep(p.lat,p.lon));
function catmull(P,seg=36){
  const out=[],marks=[0],d=(a,b)=>Math.pow(Math.hypot(b[0]-a[0],b[1]-a[1]),.5)||1e-4;
  for(let i=0;i<P.length-1;i++){
    const p0=P[Math.max(0,i-1)],p1=P[i],p2=P[i+1],p3=P[Math.min(P.length-1,i+2)];
    const t0=0,t1=t0+d(p0,p1),t2=t1+d(p1,p2),t3=t2+d(p2,p3);
    for(let k=0;k<seg;k++){
      const t=t1+(t2-t1)*k/seg,pt=[0,1].map(j=>{
        const A1=(t1-t)/(t1-t0)*p0[j]+(t-t0)/(t1-t0)*p1[j],A2=(t2-t)/(t2-t1)*p1[j]+(t-t1)/(t2-t1)*p2[j],A3=(t3-t)/(t3-t2)*p2[j]+(t-t2)/(t3-t2)*p3[j];
        const B1=(t2-t)/(t2-t0)*A1+(t-t0)/(t2-t0)*A2,B2=(t3-t)/(t3-t1)*A2+(t-t1)/(t3-t1)*A3;
        return (t2-t)/(t2-t1)*B1+(t-t1)/(t2-t1)*B2});
      out.push(pt);
    }
    marks.push(out.length);
  }
  out.push(P[P.length-1]);
  const cum=[0];for(let i=1;i<out.length;i++)cum.push(cum[i-1]+Math.hypot(out[i][0]-out[i-1][0],out[i][1]-out[i-1][1]));
  return {p:out,cum,stopAt:marks.map(m=>cum[Math.min(m,cum.length-1)]/cum[cum.length-1])};
}
const day=catmull(repPts);
const routes=PARK.r.map(r=>{
  const p=r.t.map(([a,o])=>toPk(a,o)),cum=[0];
  for(let i=1;i<p.length;i++)cum.push(cum[i-1]+Math.hypot(p[i][0]-p[i-1][0],p[i][1]-p[i-1][1]));
  let x0=1e9,y0=1e9,x1=-1e9,y1=-1e9;p.forEach(([x,y])=>{x0=Math.min(x0,x);y0=Math.min(y0,y);x1=Math.max(x1,x);y1=Math.max(y1,y)});
  return {p,cum,box:[x0,y0,x1,y1]};
});
const pois=PARK.poi.map(([a,o,n])=>({n,xy:toPk(a,o)}));
routes.forEach(r=>{r.labels=[];const seen=new Set();pois.forEach(q=>{
  if(/Указатель|фонтан/i.test(q.n)||seen.has(q.n))return;
  const d=Math.min(...r.p.map(([x,y])=>Math.hypot(x-q.xy[0],y-q.xy[1])));
  if(d<24&&r.labels.length<5){r.labels.push(q);seen.add(q.n)}
})});
let parkAll=[1e9,1e9,-1e9,-1e9];routes.forEach(r=>{parkAll=[Math.min(parkAll[0],r.box[0]),Math.min(parkAll[1],r.box[1]),Math.max(parkAll[2],r.box[2]),Math.max(parkAll[3],r.box[3])]});
const RANGES=[[0,.3],[.3,.42],[.42,.6],[.6,.78],[.78,.94],[.94,1.01]];
const stepAt=m=>RANGES.findIndex(([a,b])=>m>=a&&m<b);
let lastStep=-1,lastM=-1,camBox=null,camMoving=false;
const mobile=()=>vw<760;
const region=()=>mobile()?[vw*.06,vh*.16,vw*.94,vh*.58]:[vw*.4,vh*.16,vw*.95,vh*.82];
function layout(){
  vw=innerWidth;vh=innerHeight;dpr=Math.min(devicePixelRatio||1,2);
  cv.width=vw*dpr;cv.height=vh*dpr;ctx.setTransform(dpr,0,0,dpr,0,0);lastM=-1;
}
const pinLen=()=>sec.offsetHeight-(stage.offsetHeight||vh);
const progress=()=>{if(fM>=0)return fM;return cl(-sec.getBoundingClientRect().top/pinLen())};
let taken=[];
function label(x,y,text,sub,alpha,side='r'){
  if(alpha<=.01)return;
  ctx.font='600 11px "JetBrains Mono",monospace';
  const w=Math.max(ctx.measureText(text.toUpperCase()).width,sub?ctx.measureText(sub).width:0),h=sub?30:16;
  if(side==='l'&&x-12-w<8)side='r';else if(side==='r'&&x+12+w>vw-8&&x-12-w>=8)side='l';
  const bx=side==='r'?x+12:x-12-w,by=y-h/2;
  if(taken.some(b=>bx<b[2]&&bx+w>b[0]&&by<b[3]&&by+h>b[1]))return;
  taken.push([bx-4,by-2,bx+w+4,by+h+2]);
  ctx.globalAlpha=alpha;ctx.textAlign='left';ctx.textBaseline='middle';
  ctx.shadowColor='rgba(4,10,20,.95)';ctx.shadowBlur=10;ctx.fillStyle='#EEF2F6';
  ctx.fillText(text.toUpperCase(),bx,y-(sub?7:0));
  if(sub){ctx.font='400 11px "JetBrains Mono",monospace';ctx.fillStyle='#F7C98B';ctx.fillText(sub,bx,y+8)}
  ctx.shadowBlur=0;ctx.globalAlpha=1;
}
function polyline(p,cum,upto,style,width,glow){
  const L=cum[cum.length-1]*upto;if(L<=0)return null;
  ctx.beginPath();ctx.moveTo(p[0][0],p[0][1]);let end=p[0];
  for(let i=1;i<p.length;i++){
    if(cum[i]>=L){const t=(L-cum[i-1])/(cum[i]-cum[i-1]||1);end=[lerp(p[i-1][0],p[i][0],t),lerp(p[i-1][1],p[i][1],t)];ctx.lineTo(end[0],end[1]);break}
    ctx.lineTo(p[i][0],p[i][1]);end=p[i];
  }
  ctx.lineCap='round';ctx.lineJoin='round';ctx.strokeStyle=style;ctx.lineWidth=width;
  if(glow){ctx.shadowColor=glow;ctx.shadowBlur=14}ctx.stroke();ctx.shadowBlur=0;
  return end;
}
const dot=(x,y,r,fill,alpha=1)=>{ctx.globalAlpha=alpha;ctx.fillStyle=fill;ctx.beginPath();ctx.arc(x,y,r,0,7);ctx.fill();ctx.globalAlpha=1};
function spark(x,y,a){ctx.globalAlpha=a;ctx.fillStyle='#FFF1DC';ctx.shadowColor='#F2A01F';ctx.shadowBlur=16;ctx.beginPath();ctx.arc(x,y,4,0,7);ctx.fill();ctx.shadowBlur=0;ctx.globalAlpha=1}
function fit(box,R,pad){const w=box[2]-box[0]+pad*2,h=box[3]-box[1]+pad*2;return {s:Math.min((R[2]-R[0])/w,(R[3]-R[1])/h),c:[(box[0]+box[2])/2,(box[1]+box[3])/2],a:[(R[0]+R[2])/2,(R[1]+R[3])/2]}}
function render(m){
  taken=[];
  ctx.fillStyle='#081221';ctx.fillRect(0,0,vw,vh);
  const step=stepAt(m),R=region(),zoom=ease(cl((m-.3)/.12));
  if(zoom<1){
    const xs=[...repPts,toRep(ELBRUS.lat,ELBRUS.lon),toRep(NALCHIK.lat,NALCHIK.lon)];
    const box=[Math.min(...xs.map(p=>p[0])),Math.min(...xs.map(p=>p[1])),Math.max(...xs.map(p=>p[0])),Math.max(...xs.map(p=>p[1]))];
    const F=fit(box,R,60),n=toRep(NALCHIK.lat,NALCHIK.lon);
    const Z=Math.pow(18,zoom),s=F.s*Z,c=[0,1].map(j=>n[j]-(n[j]-F.c[j])*(1-zoom)/Z);
    const T=(x,y)=>[F.a[0]+(x-c[0])*s,F.a[1]+(y-c[1])*s];
    const a=1-sm(cl((zoom-.5)/.4)),o=T(0,0);
    ctx.globalAlpha=a;ctx.drawImage(repImg,o[0],o[1],KBR[4]*s,KBR[5]*s);ctx.globalAlpha=1;
    const pr=sm(cl((m-.05)/.21)),pts=day.p.map(([x,y])=>T(x,y)),la=1-sm(cl((zoom-.08)/.3));
    ctx.globalAlpha=la;polyline(pts,day.cum,1,'rgba(238,242,246,.16)',1.4);
    const tip=polyline(pts,day.cum,pr,'#F2A01F',2.6,'rgba(242,160,31,.8)');ctx.globalAlpha=1;
    if(tip&&pr<1)spark(tip[0],tip[1],la);
    const e=T(...toRep(ELBRUS.lat,ELBRUS.lon));
    ctx.globalAlpha=la*.95;ctx.fillStyle='#EEF2F6';ctx.beginPath();ctx.moveTo(e[0],e[1]-7);ctx.lineTo(e[0]+6,e[1]+4);ctx.lineTo(e[0]-6,e[1]+4);ctx.closePath();ctx.fill();ctx.globalAlpha=1;
    const N=T(...n),na=a*sm(cl((m-.22)/.06));
    if(na>0)label(N[0],N[1],'Нальчик','3 маршрута в приложении',na,'r');
    label(e[0],e[1],'Эльбрус','5 642 м',la*.9,'l');
    PLACES.forEach((p,i)=>{
      const [x,y]=T(...repPts[i]),lit=pr>=day.stopAt[i]-.001;
      dot(x,y,lit?5.5:3.5,lit?'#F2A01F':'rgba(238,242,246,.6)',la);
      if(lit){ctx.globalAlpha=la;ctx.strokeStyle='rgba(242,160,31,.45)';ctx.lineWidth=1.5;ctx.beginPath();ctx.arc(x,y,11,0,7);ctx.stroke();ctx.globalAlpha=1}
      label(x,y,p.n,p.a,la*(lit?1:.4),p.side);
    });
    if(na>0){dot(N[0],N[1],4.5,'#EEF2F6',na);ctx.globalAlpha=na;ctx.strokeStyle='rgba(238,242,246,.5)';ctx.lineWidth=1;[12,20].forEach(r=>{ctx.beginPath();ctx.arc(N[0],N[1],r,0,7);ctx.stroke()});ctx.globalAlpha=1}
    setMeta(mPerPx(KBR)/s,KBR[3]-(c[1]/KBR[5])*(KBR[3]-KBR[2]),KBR[0]+(c[0]/KBR[4])*(KBR[1]-KBR[0]));
  }
  if(zoom>.5){
    const k=sm(cl((zoom-.5)/.5)),ri=step>=2&&step<=4?step-2:-1;
    const target=ri>=0?routes[ri].box:parkAll;
    if(!camBox)camBox=target.slice();
    const f=reduce?target:camBox.map((v,i)=>v+(target[i]-v)*.1);
    camMoving=f.some((v,i)=>Math.abs(v-target[i])>.4);camBox=f;
    const F=fit(f,R,70),s=F.s*(.12+.88*k),T=(x,y)=>[F.a[0]+(x-F.c[0])*s,F.a[1]+(y-F.c[1])*s],o=T(0,0);
    ctx.globalAlpha=k;ctx.drawImage(parkImg,o[0],o[1],PKB[4]*s,PKB[5]*s);ctx.globalAlpha=1;
    pois.forEach(q=>{const [x,y]=T(...q.xy);dot(x,y,2.2,'rgba(238,242,246,.55)',k)});
    const all=step===1||step===5;
    routes.forEach((r,i)=>{if(i===ri)return;ctx.globalAlpha=k;polyline(r.p.map(([x,y])=>T(x,y)),r.cum,1,all?'rgba(242,160,31,.8)':'rgba(238,242,246,.3)',all?2.2:1.5);ctx.globalAlpha=1});
    if(ri>=0){
      const r=routes[ri],pr=sm(cl((m-RANGES[step][0]-.01)/.09)),pts=r.p.map(([x,y])=>T(x,y));
      ctx.globalAlpha=k;const tip=polyline(pts,r.cum,pr,'#F2A01F',3.2,'rgba(242,160,31,.85)');ctx.globalAlpha=1;
      dot(pts[0][0],pts[0][1],5.5,'#F2A01F',k);label(pts[0][0],pts[0][1],'Старт','',k,'l');
      r.labels.forEach((q,j)=>{const [x,y]=T(...q.xy),la=k*sm(cl((pr-.12-j*.13)/.14));dot(x,y,3.5,'#EEF2F6',la);label(x,y,q.n,'',la,x>F.a[0]?'r':'l')});
      if(tip&&pr<1)spark(tip[0],tip[1],k);
      moveProfile(ri,pr);
    }
    setMeta(mPerPx(PKB)/s,PKB[3]-(F.c[1]/PKB[5])*(PKB[3]-PKB[2]),PKB[0]+(F.c[0]/PKB[4])*(PKB[1]-PKB[0]));
  }
  const open=sm(cl(m/.06));white.style.opacity=(1-sm(cl(m/.025))).toFixed(3);
  if(open<1&&!reduce){
    ctx.globalAlpha=1-open;
    FOG.forEach(f=>{const r=(f.r0+open*1.1)*Math.max(vw,vh),x=vw/2+Math.cos(f.a)*r,y=vh/2+Math.sin(f.a)*r*.7,S=f.s*Math.max(vw,vh)*(1+open);ctx.drawImage(PUFF,x-S,y-S*.7,S*2,S*1.4)});
    ctx.globalAlpha=1;
  }
  if(step!==lastStep){steps.forEach((el,i)=>el.classList.toggle('on',i===step));prof.classList.toggle('on',step>=2&&step<=4);if(step>=2&&step<=4)drawProfile(step-2);lastStep=step}
  if(step===0){const pr=sm(cl((m-.05)/.21));stopRows.forEach((li,i)=>li.classList.toggle('lit',pr>=day.stopAt[i]-.001))}
}
function setMeta(mPerScreenPx,lat,lon){
  const opts=[20,50,100,200,500,1000,2000,5000,10000,20000,50000],len=opts.find(o=>o/mPerScreenPx>=70)||opts[opts.length-1];
  scaleEl.querySelector('i').style.width=(len/mPerScreenPx).toFixed(0)+'px';
  scaleEl.querySelector('span').textContent=len>=1000?(len/1000)+' км':len+' м';
  coordEl.textContent=lat.toFixed(3)+'° N · '+lon.toFixed(3)+'° E';
}
let profFor=-1,profGeom=null;
function drawProfile(ri){
  const r=PARK.r[ri],p=r.p,W=520,H=120,lo=500,hi=770;
  const X=i=>i/(p.length-1)*W,Y=e=>H-8-(e-lo)/(hi-lo)*(H-22),d='M'+p.map((e,i)=>X(i).toFixed(1)+','+Y(e).toFixed(1)).join('L');
  profSvg.setAttribute('viewBox',`0 0 ${W} ${H}`);
  profSvg.innerHTML=`<defs><linearGradient id="pg" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F2A01F" stop-opacity=".38"/><stop offset="1" stop-color="#F2A01F" stop-opacity="0"/></linearGradient></defs>
    <line x1="0" x2="${W}" y1="${Y(600)}" y2="${Y(600)}" class="pgrid"/><line x1="0" x2="${W}" y1="${Y(700)}" y2="${Y(700)}" class="pgrid"/>
    <text x="${W}" y="${Y(700)-5}" class="plab" text-anchor="end">700 м</text><text x="${W}" y="${Y(600)-5}" class="plab" text-anchor="end">600 м</text>
    <path d="${d}L${W},${H}L0,${H}Z" fill="url(#pg)"/><path d="${d}" class="pline"/><circle r="4.5" class="pdot" id="pdot"/>`;
  $('mproflen').textContent=(r.len/1000).toFixed(1).replace('.',',')+' км';
  profGeom={X,Y,p};profFor=ri;
}
function moveProfile(ri,pr){
  if(profFor!==ri)drawProfile(ri);
  const {X,Y,p}=profGeom,f=pr*(p.length-1),i=Math.floor(f),e=lerp(p[i],p[Math.min(p.length-1,i+1)],f-i),d=$('pdot');
  if(d){d.setAttribute('cx',X(f));d.setAttribute('cy',Y(e))}
}
const hash=(x,y)=>{let h=x*374761393+y*668265263;h=(h^(h>>>13))*1274126177;return((h^(h>>>16))>>>0)/4294967295};
const PUFF=document.createElement('canvas');PUFF.width=PUFF.height=128;
{const c=PUFF.getContext('2d'),g=c.createRadialGradient(64,64,0,64,64,64);g.addColorStop(0,'rgba(244,247,248,1)');g.addColorStop(.5,'rgba(244,247,248,.6)');g.addColorStop(1,'rgba(244,247,248,0)');c.fillStyle=g;c.fillRect(0,0,128,128)}
const FOG=Array.from({length:22},(_,i)=>({a:i/22*Math.PI*2+hash(i,7)*.4,r0:hash(i,3)*.25,s:.25+hash(i,5)*.25}));
{const n=document.createElement('canvas');n.width=n.height=160;const x=n.getContext('2d'),d=x.createImageData(160,160);
 for(let i=0;i<d.data.length;i+=4){const v=hash(i,11)*255;d.data[i]=d.data[i+1]=d.data[i+2]=v;d.data[i+3]=255}x.putImageData(d,0,0);
 $('mgrain').style.backgroundImage=`url(${n.toDataURL()})`}
PARK.r.forEach((r,i)=>{
  const el=document.querySelector(`.mstep[data-route="${i}"]`);if(!el)return;
  el.querySelector('[data-f="len"]').textContent=(r.len/1000).toFixed(1).replace('.',',')+' км';
  el.querySelector('[data-f="gain"]').textContent=r.gain+' м';
  el.querySelector('[data-f="range"]').textContent=r.min+'–'+r.max+' м';
  el.querySelector('.mmodes').innerHTML=r.modes.map(x=>`<span>${x}</span>`).join('');
});
let looping=false;
function loop(){
  const r=sec.getBoundingClientRect(),pinned=fM>=0||r.top<=1,onScreen=pinned&&r.bottom>0;
  stage.style.visibility=onScreen?'visible':'hidden';
  if(ready<2||!onScreen){looping=false;return}
  const m=progress();
  if(m!==lastM||camMoving){render(m);lastM=m}
  requestAnimationFrame(loop);
}
function kick(){if(!looping){looping=true;requestAnimationFrame(loop)}}
if(fM>=0){const j=$('journey');if(j)j.style.display='none';sec.style.marginTop='0'}
const fade=$('mfade');
function jumpTo(m){
  fade.classList.add('show');stage.classList.add('arrive');
  scrollTo({top:sec.offsetTop+pinLen()*m,behavior:'instant'});
  lastStep=-1;kick();
  void fade.offsetWidth;setTimeout(()=>fade.classList.remove('show'),60);
  setTimeout(()=>stage.classList.remove('arrive'),1600);
}
document.querySelectorAll('a[data-go]').forEach(a=>a.addEventListener('click',e=>{e.preventDefault();jumpTo(parseFloat(a.dataset.go))}));
if(location.hash==='#map')addEventListener('load',()=>jumpTo(.28));
if(params.has('go'))addEventListener('load',()=>setTimeout(()=>jumpTo(parseFloat(params.get('go'))),300));
layout();
addEventListener('resize',()=>{layout();kick()});
addEventListener('scroll',kick,{passive:true});
})();
