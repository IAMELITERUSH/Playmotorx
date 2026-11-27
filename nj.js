/* ===========================================================
   MotorX — New Jersey (real OpenStreetMap data, streamed in tiles)
   Map data © OpenStreetMap contributors (ODbL).
   Loaded after the main script; uses its globals (THREE, scene, P, teleport, ...).
   =========================================================== */
(function(){
'use strict';
const M=window.MXENV;
const NJ=window.NJ={on:false,ready:false,idx:null,tiles:new Map(),loading:new Set(),group:null,hidden:null,mask:null,frame:0,lastTile:'',stats:{tiles:0,bld:0}};
const T=400,LOAD_R=760,KEEP_R=1250;
const KX0=111320,KY=110574;
let KX=KX0,LAT0=40.7,LON0=-74.09;
const toXZ=(lat,lon)=>[(lon-LON0)*KX,-(lat-LAT0)*KY];

/* ---------- materials ---------- */
let matFlat,matBld,matWater,waterMesh,winTex,winEmi,matLamp,matGlow,matSky,skyline;
function makeWinTex(){
  const S=256,c=document.createElement('canvas');c.width=c.height=S;const x=c.getContext('2d');
  x.fillStyle='#ffffff';x.fillRect(0,0,S,S);
  const e=document.createElement('canvas');e.width=e.height=S;const y=e.getContext('2d');
  y.fillStyle='#000';y.fillRect(0,0,S,S);
  let seed=7;const rnd=()=>{seed=(seed*16807)%2147483647;return seed/2147483647;};
  for(let a=0;a<4;a++)for(let b=0;b<4;b++){
    const px=a*64,py=b*64;
    x.fillStyle=(rnd()<.5)?'#6f8aa6':'#5b7794';x.fillRect(px+13,py+12,38,38);
    x.fillStyle='#c9d6e3';x.fillRect(px+13,py+12,38,5);
    x.fillStyle='#3b4f66';x.fillRect(px+31,py+12,2,38);
    if(rnd()<.42){y.fillStyle=rnd()<.8?'#ffd98a':'#bfe0ff';y.fillRect(px+13,py+12,38,38);}
  }
  winTex=new THREE.CanvasTexture(c);winEmi=new THREE.CanvasTexture(e);
  for(const t of[winTex,winEmi]){t.wrapS=t.wrapT=THREE.RepeatWrapping;t.anisotropy=4;}
}
function initMats(){
  if(matFlat)return;
  makeWinTex();
  matFlat=new THREE.MeshLambertMaterial({vertexColors:true});
  matBld=new THREE.MeshLambertMaterial({vertexColors:true,map:winTex,emissive:new THREE.Color(0,0,0),emissiveMap:winEmi});
  matWater=new THREE.MeshLambertMaterial({color:0x2f6b99});
  matLamp=new THREE.MeshBasicMaterial({vertexColors:true,color:0x555555});
  {const c=document.createElement('canvas');c.width=c.height=64;const x=c.getContext('2d');const g=x.createRadialGradient(32,32,1,32,32,31);g.addColorStop(0,'rgba(255,255,255,1)');g.addColorStop(.4,'rgba(255,255,255,.35)');g.addColorStop(1,'rgba(255,255,255,0)');x.fillStyle=g;x.fillRect(0,0,64,64);
   matGlow=new THREE.MeshBasicMaterial({map:new THREE.CanvasTexture(c),transparent:true,depthWrite:false,blending:THREE.AdditiveBlending,color:0xffc47a,opacity:0,fog:true});}
  matSky=new THREE.MeshLambertMaterial({vertexColors:true,map:winTex,emissive:new THREE.Color(0,0,0),emissiveMap:winEmi,fog:false});
  waterMesh=new THREE.Mesh(new THREE.PlaneGeometry(60000,60000).rotateX(-Math.PI/2),matWater);
  waterMesh.position.y=-.35;waterMesh.frustumCulled=false;waterMesh.receiveShadow=false;
}

/* ---------- geometry helpers ---------- */
function hash(a,b){let h=(a*374761393+b*668265263)|0;h=(h^(h>>>13))*1274126177|0;return((h^(h>>>16))>>>0)/4294967296;}
const ROAD_W={0:9,1:5,2:8.5,3:5,4:7.5,5:4.6,6:7,7:4.6,8:6.4,9:4.4,10:6,11:6,12:4.6,13:3.8};
const ROAD_COL={0:0x3b3e43,1:0x3f4247,2:0x3d4045,3:0x404348,4:0x43464b,5:0x45484d,6:0x474a4f,7:0x474a4f,8:0x4a4d52,9:0x4a4d52,10:0x4c4f54,11:0x4e5156,12:0x505358,13:0x55585d};
class Buf{constructor(){this.p=[];this.n=[];this.c=[];this.u=[];this.i=[];}
  v(x,y,z,nx,ny,nz,r,g,b,u,w){const k=this.p.length/3;this.p.push(x,y,z);this.n.push(nx,ny,nz);this.c.push(r,g,b);this.u.push(u||0,w||0);return k;}
  geo(uv){const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(this.p,3));g.setAttribute('normal',new THREE.Float32BufferAttribute(this.n,3));g.setAttribute('color',new THREE.Float32BufferAttribute(this.c,3));
    if(uv)g.setAttribute('uv',new THREE.Float32BufferAttribute(this.u,2));g.setIndex(this.i);g.computeBoundingSphere();return g;}}
const _c=new THREE.Color();
function col(hex,j,rr){_c.setHex(hex);const f=1+(j||0)*(rr-.5);return[_c.r*f,_c.g*f,_c.b*f];}
// add a triangle, flipping so the face normal points along (nx,ny,nz)
function tri(B,a,b,c,nx,ny,nz){
  const p=B.p;const ax=p[a*3],ay=p[a*3+1],az=p[a*3+2],bx=p[b*3],by=p[b*3+1],bz=p[b*3+2],cx=p[c*3],cy=p[c*3+1],cz=p[c*3+2];
  const ux=bx-ax,uy=by-ay,uz=bz-az,vx=cx-ax,vy=cy-ay,vz=cz-az;
  const gx=uy*vz-uz*vy,gy=uz*vx-ux*vz,gz=ux*vy-uy*vx;
  if(gx*nx+gy*ny+gz*nz>=0)B.i.push(a,b,c);else B.i.push(a,c,b);
}
function ribbon(B,pts,w,y,rgb){
  const n=pts.length/2;if(n<2)return;
  let base=-1;
  for(let i=0;i<n;i++){
    const i0=Math.max(0,i-1),i1=Math.min(n-1,i+1);
    let tx=pts[i1*2]-pts[i0*2],tz=pts[i1*2+1]-pts[i0*2+1];const L=Math.hypot(tx,tz)||1;tx/=L;tz/=L;
    const nx=-tz*w/2,nz=tx*w/2;
    const a=B.v(pts[i*2]+nx,y,pts[i*2+1]+nz,0,1,0,rgb[0],rgb[1],rgb[2]);
    const b=B.v(pts[i*2]-nx,y,pts[i*2+1]-nz,0,1,0,rgb[0],rgb[1],rgb[2]);
    if(i>0){tri(B,a-2,b-2,a,0,1,0);tri(B,b-2,b,a,0,1,0);}
    base=a;
  }
}
function polyFlat(B,pts,y,rgb){
  const n=pts.length/2;if(n<3)return;
  const cont=[];for(let i=0;i<n;i++)cont.push(new THREE.Vector2(pts[i*2],pts[i*2+1]));
  let faces;try{faces=THREE.ShapeUtils.triangulateShape(cont,[]);}catch(e){return;}
  const k0=B.p.length/3;
  for(let i=0;i<n;i++)B.v(pts[i*2],y,pts[i*2+1],0,1,0,rgb[0],rgb[1],rgb[2]);
  for(const f of faces)tri(B,k0+f[0],k0+f[1],k0+f[2],0,1,0);
}
const BPAL=[0xb9623f,0xc8b79a,0x9aa1a8,0xd8d0c0,0xa6745a,0x8c8f94,0xcdbf9d,0x7e8794,0xe0d6c3,0xb08060];
function building(B,pts,hgt,kind,seedA,seedB){
  const n=pts.length/2;if(n<3)return false;
  // area sign
  let s=0;for(let i=0;i<n;i++){const j=(i+1)%n;s+=pts[i*2]*pts[j*2+1]-pts[j*2]*pts[i*2+1];}
  const r1=hash(seedA,seedB),r2=hash(seedB,seedA+7);
  let H=hgt;
  if(!H){
    switch(kind){case 0:H=5.5+r1*3.5;break;case 1:H=11+r1*18;break;case 2:H=7+r1*8;break;case 3:H=16+r1*40;break;case 4:H=8+r1*5;break;case 5:H=9+r1*8;break;case 6:H=9+r1*4;break;default:H=6+r1*9;}
    // bigger footprints tend to be taller
    const area=Math.abs(s)/2;if(kind>=2&&kind!==4&&area>1400)H+=r2*18;
  }
  H=Math.max(3,Math.min(H,260));
  const wallCol=BPAL[Math.floor(r2*BPAL.length)];
  const wc=col(wallCol,1,r1),rc=col(0x5a5d62,1,r2);
  // roof
  const cont=[];for(let i=0;i<n;i++)cont.push(new THREE.Vector2(pts[i*2],pts[i*2+1]));
  let faces;try{faces=THREE.ShapeUtils.triangulateShape(cont,[]);}catch(e){faces=null;}
  if(!faces||!faces.length)return false;
  const k0=B.p.length/3;
  for(let i=0;i<n;i++)B.v(pts[i*2],H,pts[i*2+1],0,1,0,rc[0],rc[1],rc[2],.012,.012);
  for(const f of faces)tri(B,k0+f[0],k0+f[1],k0+f[2],0,1,0);
  // walls
  let acc=0;
  for(let i=0;i<n;i++){
    const j=(i+1)%n,x0=pts[i*2],z0=pts[i*2+1],x1=pts[j*2],z1=pts[j*2+1];
    const dx=x1-x0,dz=z1-z0,L=Math.hypot(dx,dz);if(L<.05)continue;
    let nx=dz/L,nz=-dx/L;if(s<0){nx=-nx;nz=-nz;}
    const u0=acc/16,u1=(acc+L)/16,v1=H/13.2;acc+=L;
    const a=B.v(x0,0,z0,nx,0,nz,wc[0],wc[1],wc[2],u0,0);
    const b=B.v(x1,0,z1,nx,0,nz,wc[0],wc[1],wc[2],u1,0);
    const c=B.v(x1,H,z1,nx,0,nz,wc[0],wc[1],wc[2],u1,v1);
    const d=B.v(x0,H,z0,nx,0,nz,wc[0],wc[1],wc[2],u0,v1);
    tri(B,a,b,c,nx,0,nz);tri(B,a,c,d,nx,0,nz);
  }
  return true;
}

function boxB(B,cx,y0,cz,w,h,d,rgb,uv){
  const x0=cx-w/2,x1=cx+w/2,z0=cz-d/2,z1=cz+d/2,y1=y0+h;
  const F=[[[x0,y0,z1],[x1,y0,z1],[x1,y1,z1],[x0,y1,z1],0,0,1],[[x1,y0,z0],[x0,y0,z0],[x0,y1,z0],[x1,y1,z0],0,0,-1],[[x1,y0,z1],[x1,y0,z0],[x1,y1,z0],[x1,y1,z1],1,0,0],[[x0,y0,z0],[x0,y0,z1],[x0,y1,z1],[x0,y1,z0],-1,0,0],[[x0,y1,z1],[x1,y1,z1],[x1,y1,z0],[x0,y1,z0],0,1,0]];
  for(const f of F){const k=B.p.length/3;for(let q=0;q<4;q++)B.v(f[q][0],f[q][1],f[q][2],f[4],f[5],f[6],rgb[0],rgb[1],rgb[2],uv?(q===1||q===2?w/16:0):0,uv?(q>=2?h/13.2:0):0);tri(B,k,k+1,k+2,f[4],f[5],f[6]);tri(B,k,k+2,k+3,f[4],f[5],f[6]);}
}
function lamps(F,L,G,pts,w){
  const n=pts.length/2;let acc=0,next=14,side=1;
  for(let i=0;i<n-1;i++){
    const x0=pts[i*2],z0=pts[i*2+1],x1=pts[i*2+2],z1=pts[i*2+3],dx=x1-x0,dz=z1-z0,len=Math.hypot(dx,dz);if(len<.1)continue;
    const tx=dx/len,tz=dz/len;
    while(acc+len>=next){
      const f=(next-acc)/len,px=x0+dx*f,pz=z0+dz*f,off=(w/2+1.3)*side,lx=px-tz*off,lz=pz+tx*off;
      boxB(F,lx,0,lz,.16,7.2,.16,[.25,.26,.28]);
      boxB(L,lx-(-tz*side)*-.0+(-tz)*(-side)*.0,7.1,lz,.8,.18,.8,[1,.92,.7]);
      // glow pool on the road under the lamp
      const gx=lx+tz*side*2.2,gz=lz-tx*side*2.2,r=7;
      const k=G.v(gx-r,.075,gz-r,0,1,0,1,1,1,0,0);G.v(gx+r,.075,gz-r,0,1,0,1,1,1,1,0);G.v(gx+r,.075,gz+r,0,1,0,1,1,1,1,1);G.v(gx-r,.075,gz+r,0,1,0,1,1,1,0,1);
      tri(G,k,k+1,k+2,0,1,0);tri(G,k,k+2,k+3,0,1,0);
      side=-side;next+=44;
    }
    acc+=len;
  }
}
/* ---------- tile build ---------- */
function polyPts(a){const o=new Array(a.length);for(let i=0;i<a.length;i++)o[i]=a[i]/10;return o;}
function inPoly(x,z,P){let c=false;const n=P.length/2;for(let i=0,j=n-1;i<n;j=i++){const xi=P[i*2],zi=P[i*2+1],xj=P[j*2],zj=P[j*2+1];if(((zi>z)!==(zj>z))&&(x<(xj-xi)*(z-zi)/(zj-zi)+xi))c=!c;}return c;}
function buildTile(key,data){
  const [ti,tj]=key.split('_').map(Number),ox=ti*T,oz=tj*T;
  const g=new THREE.Group();g.position.set(ox,0,oz);
  const F=new Buf(),Bd=new Buf(),Lm=new Buf(),Gl=new Buf();
  // ground cells (land mask)
  const m=NJ.mask,cs=m.cell;
  const dens=new Map();
  for(const b of data.b||[]){const p=b[2];const ca=Math.floor(p[0]/10/cs),cb=Math.floor(p[1]/10/cs),kk=ca+','+cb;dens.set(kk,(dens.get(kk)||0)+1);}
  for(let a=0;a<T/cs;a++)for(let b=0;b<T/cs;b++){
    const cx=ox+a*cs,cz=oz+b*cs;
    if(landAt(cx+cs/2,cz+cs/2)){
      const dn=dens.get(a+','+b)||0;
      const gc=dn>0?col(0x6f726d,.5,hash(Math.floor(cx/cs),Math.floor(cz/cs))):col(0x4d7a3f,1,hash(Math.floor(cx/cs),Math.floor(cz/cs)));
      const k=F.v(a*cs,0,b*cs,0,1,0,gc[0],gc[1],gc[2]);F.v((a+1)*cs,0,b*cs,0,1,0,gc[0],gc[1],gc[2]);F.v((a+1)*cs,0,(b+1)*cs,0,1,0,gc[0],gc[1],gc[2]);F.v(a*cs,0,(b+1)*cs,0,1,0,gc[0],gc[1],gc[2]);
      tri(F,k,k+1,k+2,0,1,0);tri(F,k,k+2,k+3,0,1,0);
    }
  }
  for(const p of data.p||[])polyFlat(F,polyPts(p),.015,col(0x3f7a38,.6,Math.random()));
  for(const p of data.w||[])polyFlat(F,polyPts(p),.025,col(0x2f6b99,0,0));
  for(const l of data.l||[])ribbon(F,polyPts(l),1.6,.035,col(0x2a2a2d,0,0));
  // roads, drawn big-to-small so majors win overlaps
  const roads=(data.r||[]).slice().sort((a,b)=>b[0]-a[0]);
  for(const r of roads){
    const t=r[0],ln=r[1],fl=r[2];if(fl&4)continue;
    let w=ROAD_W[t]||5;if(ln)w=Math.max(w,ln*3.3*((fl&1)?1:1));if(!(fl&1)&&t<=3)w=Math.max(w,7);
    const y=.04+(13-t)*.0035+((fl&2)?.05:0);
    const pts=polyPts(r[3]);
    ribbon(F,pts,w,y,col(ROAD_COL[t]||0x4a4d52,0,0));
    if(t<=8&&!(fl&2))lamps(F,Lm,Gl,pts,w);
    if(!(fl&1)&&t<=12&&t>=2)ribbon(F,pts,.2,y+.01,col(0xd6b53a,0,0));
    else if((fl&1)&&t<=3)ribbon(F,pts,.16,y+.01,col(0xe8e8e8,0,0));
  }
  // buildings (+ collision records)
  const col2=[];
  for(const b of data.b||[]){
    const pts=polyPts(b[2]);
    if(building(Bd,pts,b[1]/10,b[0],Math.floor((ox+pts[0])*3.1),Math.floor((oz+pts[1])*3.1))){
      let x0=1e9,z0=1e9,x1=-1e9,z1=-1e9;for(let i=0;i<pts.length;i+=2){x0=Math.min(x0,pts[i]);x1=Math.max(x1,pts[i]);z0=Math.min(z0,pts[i+1]);z1=Math.max(z1,pts[i+1]);}
      col2.push({x0:x0+ox,x1:x1+ox,z0:z0+oz,z1:z1+oz,p:pts,ox,oz});
    }
  }
  const mf=new THREE.Mesh(F.geo(false),matFlat);mf.receiveShadow=true;mf.matrixAutoUpdate=false;g.add(mf);
  if(Bd.i.length){const mb=new THREE.Mesh(Bd.geo(true),matBld);mb.castShadow=true;mb.receiveShadow=true;mb.matrixAutoUpdate=false;g.add(mb);}
  if(Lm.i.length){const ml=new THREE.Mesh(Lm.geo(false),matLamp);ml.matrixAutoUpdate=false;g.add(ml);}
  if(Gl.i.length){const mg=new THREE.Mesh(Gl.geo(true),matGlow);mg.matrixAutoUpdate=false;mg.renderOrder=3;g.add(mg);}
  g.updateMatrixWorld(true);
  g.children.forEach(c=>{c.matrixAutoUpdate=false;});
  NJ.group.add(g);
  NJ.stats.bld+=col2.length;
  const ways=[];
  for(const r of data.r||[]){if(r[0]>11||(r[2]&6))continue;const pts=polyPts(r[3]);for(let q=0;q<pts.length;q+=2){pts[q]+=ox;pts[q+1]+=oz;}ways.push({pts,t:r[0],oneway:!!(r[2]&1)});}
  return{key,group:g,col:col2,ways};
}
function disposeTile(t){NJ.group.remove(t.group);t.group.traverse(o=>{if(o.geometry)o.geometry.dispose();});NJ.stats.bld-=t.col.length;}

/* ---------- land mask + collisions ---------- */
function landAt(x,z){
  const m=NJ.mask;if(!m)return true;
  const a=Math.floor(x/m.cell)-m.a0,b=Math.floor(z/m.cell)-m.b0;
  if(a<0||b<0||a>=m.W||b>=m.H)return false;
  const i=b*m.W+a;return(m.bits[i>>3]>>(i&7))&1;
}
NJ.landAt=landAt;
NJ.blocked=function(x,z){
  if(!landAt(x,z))return true;
  const t=NJ.tiles.get(Math.floor(x/T)+'_'+Math.floor(z/T));
  if(!t||t.loading)return false;
  const L=t.col;
  for(let q=0;q<L.length;q++){const b=L[q];if(x<b.x0||x>b.x1||z<b.z0||z>b.z1)continue;if(inPoly(x-b.ox,z-b.oz,b.p))return true;}
  return false;
};

/* ---------- streaming ---------- */
async function loadTile(key){
  if(NJ.tiles.has(key)||NJ.loading.has(key))return;
  if(!NJ.idxSet.has(key))return;
  NJ.loading.add(key);
  try{
    const r=await fetch('nj/t/'+key+'.json');const data=await r.json();
    if(NJ.on&&!NJ.tiles.has(key)){sampleRoads(key,data);NJ.tiles.set(key,buildTile(key,data));NJ.stats.tiles=NJ.tiles.size;}
  }catch(e){console.warn('nj tile',key,e&&e.message);}
  NJ.loading.delete(key);
}
function stream(px,pz){
  const need=[];
  const ri=Math.ceil(LOAD_R/T);
  const ci=Math.floor(px/T),cj=Math.floor(pz/T);
  for(let i=ci-ri;i<=ci+ri;i++)for(let j=cj-ri;j<=cj+ri;j++){
    const cx=i*T+T/2,cz=j*T+T/2;const d=Math.hypot(cx-px,cz-pz);
    if(d<LOAD_R+T*.5)need.push([d,i+'_'+j]);
  }
  need.sort((a,b)=>a[0]-b[0]);
  let started=0;for(const[,k]of need){if(NJ.loading.size>=3)break;if(!NJ.tiles.has(k)&&!NJ.loading.has(k)&&NJ.idxSet.has(k)){loadTile(k);started++;}}
  for(const[k,t]of NJ.tiles){const[i,j]=k.split('_').map(Number);if(Math.hypot(i*T+T/2-px,j*T+T/2-pz)>KEEP_R){disposeTile(t);NJ.tiles.delete(k);}}
  NJ.stats.tiles=NJ.tiles.size;
}

/* ---------- Manhattan skyline across the Hudson (procedural, fog-free) ---------- */
function buildSkyline(){
  const B=new Buf();let seed=99;const rnd=()=>{seed=(seed*16807)%2147483647;return seed/2147483647;};
  const pal=[0x8d96a3,0x9aa3ae,0x7c8794,0xa59f96,0x6f7b8a,0xb0b5ba];
  // spine of Manhattan: Battery -> Midtown -> Harlem (lat,lon)
  const spine=[[40.7033,-74.0170],[40.7127,-74.0134],[40.7300,-74.0040],[40.7484,-73.9857],[40.7680,-73.9780],[40.8000,-73.9560],[40.8300,-73.9400]].map(p=>toXZ(p[0],p[1]));
  // landmark towers (lat,lon,height,width)
  const tow=[[40.7127,-74.0134,420,40],[40.7484,-73.9857,380,50],[40.7558,-73.9866,250,42],[40.7527,-73.9772,210,40],[40.7614,-73.9776,260,38],[40.7060,-74.0088,180,45]];
  const addB=(x,z,w,d,h,c)=>{const cc=col(c,1,rnd());boxB(B,x,-.3,z,w,h+.3,d,cc,true);};
  for(let i=0;i<spine.length-1;i++){
    const a=spine[i],b=spine[i+1],len=Math.hypot(b[0]-a[0],b[1]-a[1]),n=Math.floor(len/38);
    const tx=(b[0]-a[0])/len,tz=(b[1]-a[1])/len,nx=-tz,nz=tx;
    // downtown (i<2) and midtown (i 2-3) are the tallest
    const base=i<2?90:i<4?110:i<5?48:34;
    for(let k=0;k<n;k++){
      const f=k/n,cx=a[0]+tx*len*f,cz=a[1]+tz*len*f;
      for(let q=-2;q<=2;q++){
        const off=q*34+(rnd()-.5)*14,px=cx+nx*off,pz=cz+nz*off;
        const edge=Math.abs(q)===2;
        const h=(base*(edge?.55:1))*(.35+rnd()*1.15)*(rnd()<.06?2.2:1);
        addB(px,pz,22+rnd()*18,22+rnd()*18,Math.max(14,h),pal[Math.floor(rnd()*pal.length)]);
      }
    }
  }
  for(const t of tow){const p=toXZ(t[0],t[1]);addB(p[0],p[1],t[3],t[3],t[2],0xaab2bb);boxB(B,p[0],t[2]-.3,p[1],t[3]*.45,t[2]*.16,t[3]*.45,col(0xaab2bb,0,0),true);}
  // island slab
  const slab=[];for(const p of spine)slab.push(p);
  for(let i=0;i<spine.length-1;i++){const a=spine[i],b=spine[i+1],len=Math.hypot(b[0]-a[0],b[1]-a[1]),tx=(b[0]-a[0])/len,tz=(b[1]-a[1])/len;
    const w=i<5?1300:900;ribbon(B,[a[0]-tx*80,a[1]-tz*80,b[0]+tx*80,b[1]+tz*80],w,-.2,col(0x666a70,0,0));}
  const m=new THREE.Mesh(B.geo(true),matSky);m.frustumCulled=false;m.matrixAutoUpdate=false;return m;
}

/* ---------- ambient traffic on the real roads ---------- */
const TR={cars:[],max:14,adj:null};
function roadGraph(){
  // nodes keyed by rounded point, edges = polylines from loaded tiles
  const ways=[];
  for(const[key,t]of NJ.tiles){for(const w of t.ways||[])ways.push(w);}
  return ways;
}
function spawnTraffic(){
  if(!M.buildCar||!M.CARS)return;
  const ways=roadGraph();if(!ways.length)return;
  const specs=M.CARS.filter(c=>c.price<=60000&&['sedan','hatch','suv','coupe','pickup','wagon'].includes(c.body));
  const hexes=['#c9ced4','#1b1d21','#8d1c1c','#1f4d8f','#d9d9d9','#4a4f55','#2c6e49','#e8c547'];
  for(let tries=0;tries<12&&TR.cars.length<TR.max;tries++){
    const w=ways[Math.floor(Math.random()*ways.length)];
    const wp=w.pts;const mid=wp.length>>2;
    const sx=wp[mid*2],sz=wp[mid*2+1];
    const d=Math.hypot(sx-M.P.x,sz-M.P.z);if(d<90||d>520)continue;
    const spec=specs[Math.floor(Math.random()*specs.length)];
    const o=M.buildCar(spec.body,hexes[Math.floor(Math.random()*hexes.length)],false,false,spec);
    M.scene.add(o.root);NJ.group.add(o.root);
    const dir=w.oneway||Math.random()<.5?1:-1;
    TR.cars.push({o,w,i:Math.max(0,Math.min(mid,wp.length/2-2)),f:0,dir,v:0,top:(w.t<=4?15:w.t<=8?11:8)*(.8+Math.random()*.4)});
  }
}
function stepCar(c,dt){
  const w=c.w,wp=w.pts,n=wp.length/2;
  // segment endpoints along direction
  let i=c.i,j=i+c.dir;
  if(j<0||j>=n){ // end of way: hop to a connected way or turn around
    const ex=wp[(c.dir>0?n-1:0)*2],ez=wp[(c.dir>0?n-1:0)*2+1];
    let nxt=null;const cand=[];
    for(const[,t]of NJ.tiles)for(const w2 of t.ways||[]){if(w2===w||w2.t>11)continue;
      const a0=Math.hypot(w2.pts[0]-ex,w2.pts[1]-ez),a1=Math.hypot(w2.pts[w2.pts.length-2]-ex,w2.pts[w2.pts.length-1]-ez);
      if(a0<2.5)cand.push([w2,0,1]);else if(a1<2.5&&!w2.oneway)cand.push([w2,w2.pts.length/2-1,-1]);}
    if(cand.length){const r=cand[Math.floor(Math.random()*cand.length)];c.w=r[0];c.i=r[1];c.dir=r[2];c.f=0;}else{c.dir=-c.dir;c.i=c.dir>0?0:n-1;if(w.oneway){c.dead=true;}}
    return;
  }
  const ax=wp[i*2],az=wp[i*2+1],bx=wp[j*2],bz=wp[j*2+1],L=Math.hypot(bx-ax,bz-az)||1;
  // slow for the player ahead
  const px=M.P.x-(ax+(bx-ax)*c.f/L),pz=M.P.z-(az+(bz-az)*c.f/L);
  const tx=(bx-ax)/L,tz=(bz-az)/L,ahead=px*tx+pz*tz,side=Math.abs(-px*tz+pz*tx);
  let want=c.top;if(ahead>0&&ahead<16&&side<3.4)want=0;
  c.v+=(want-c.v)*Math.min(1,dt*(want<c.v?3:.8));
  c.f+=c.v*dt;
  if(c.f>=L){c.i=j;c.f-=L;}
  const k=Math.min(1,c.f/L),wdt=ROAD_W[c.w.t]||5,off=c.w.oneway?0:wdt*.22;
  const x=ax+(bx-ax)*k+tz*off*-1*-1*0+(-tz)*(-off)*0+tz*off,z=az+(bz-az)*k-tx*off;
  c.o.root.position.set(x,0,z);c.o.root.rotation.y=Math.atan2(tx,tz);
  c.x=x;c.z=z;
  // gentle bump with the player
  const dx=M.P.x-x,dz=M.P.z-z,dd=Math.hypot(dx,dz);
  if(dd<3.4&&dd>.01){M.P.vx*=.86;M.P.vz*=.86;M.P.x+=dx/dd*.12;M.P.z+=dz/dd*.12;}
}
NJ.traffic=TR;
function trafficUpdate(dt){
  if(NJ.frame%40===0&&TR.cars.length<TR.max)spawnTraffic();
  for(let q=TR.cars.length-1;q>=0;q--){
    const c=TR.cars[q];stepCar(c,dt);
    const d=Math.hypot((c.x||0)-M.P.x,(c.z||0)-M.P.z);
    if(c.dead||d>700){NJ.group.remove(c.o.root);try{c.o.root.traverse(o=>{if(o.geometry&&o.geometry.dispose)o.geometry.dispose();});}catch(e){}TR.cars.splice(q,1);}
  }
}

/* ---------- hide / show the old city ---------- */
function keepVisible(o){
  if(o===NJ.group||o===waterMesh)return true;
  if(o.isLight||o.isCamera)return true;
  if(skyline&&o===skyline)return true;
  return o===M.carRoot||o===M.skyDome||o===M.sunMesh||o===M.moonMesh||o===M.stars||o===M.clouds;
}
function hideOld(){
  if(!NJ.hidden)NJ.hidden=new Map();
  for(const o of M.scene.children){if(keepVisible(o))continue;if(o.visible&&!NJ.hidden.has(o))NJ.hidden.set(o,true);o.visible=false;}
}
function restoreOld(){
  if(NJ.hidden){for(const o of NJ.hidden.keys())o.visible=true;NJ.hidden=null;}
}

/* ---------- enter / exit ---------- */
NJ.enter=async function(){
  if(NJ.on)return true;
  M.toast('Loading New Jersey…',2500);
  initMats();
  if(!NJ.idx){
    try{
      const r=await fetch('nj/index.json');NJ.idx=await r.json();
    }catch(e){M.toast('Could not load New Jersey map',3000);return false;}
    LAT0=NJ.idx.origin[0];LON0=NJ.idx.origin[1];KX=KX0*Math.cos(LAT0*Math.PI/180);
    NJ.idxSet=new Set(NJ.idx.tiles);
    const m=NJ.idx.mask,bin=atob(m.bits),bits=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)bits[i]=bin.charCodeAt(i);
    NJ.mask={cell:m.cell,a0:m.a0,b0:m.b0,W:m.W,H:m.H,bits};
  }
  NJ.group=new THREE.Group();NJ.group.name='nj';M.scene.add(NJ.group);M.scene.add(waterMesh);
  if(!skyline)skyline=buildSkyline();M.scene.add(skyline);
  NJ.farOld=M.camera.far;M.camera.far=11000;M.camera.updateProjectionMatrix();
  NJ.on=true;{const mm=document.getElementById('mini');if(mm)mm.style.visibility='hidden';}
  NJ.saved={x:M.P.x,z:M.P.z,h:M.P.h};
  // Bayonne, Broadway
  const sp=toXZ(40.6693,-74.1143);
  NJ.spawn=sp;
  hideOld();
  M.teleport(sp[0],sp[1],0);
  stream(sp[0],sp[1]);
  // wait for the first tiles
  const t0=performance.now();
  while((NJ.loading.size||NJ.tiles.size<3)&&performance.now()-t0<12000)await new Promise(r=>setTimeout(r,120));
  snapToRoad();
  NJ.ready=true;
  M.toast('Welcome to New Jersey — Bayonne',3500);
  return true;
};
NJ.exit=function(){
  if(!NJ.on)return;
  NJ.on=false;NJ.ready=false;{const mm=document.getElementById('mini');if(mm)mm.style.visibility='';}
  for(const[,t]of NJ.tiles)disposeTile(t);NJ.tiles.clear();
  M.scene.remove(NJ.group);M.scene.remove(waterMesh);if(skyline)M.scene.remove(skyline);if(NJ.farOld){M.camera.far=NJ.farOld;M.camera.updateProjectionMatrix();}for(const c of TR.cars)M.scene.remove(c.o.root);TR.cars.length=0;
  restoreOld();
  M.teleport(-3.6,-60,0);
  M.toast('Back to MotorCities',2500);
};
function snapToRoad(){
  // find the nearest road vertex among loaded tiles and face along it
  let best=1e12,bx=M.P.x,bz=M.P.z,bh=0;
  const found=NJ.roadSample;
  if(found&&found.length){for(const s of found){const d=(s.x-M.P.x)**2+(s.z-M.P.z)**2;if(d<best&&!NJ.blocked(s.x,s.z)){best=d;bx=s.x;bz=s.z;bh=s.h;}}}
  M.teleport(bx,bz,bh);
}
NJ.roadSample=[];
function sampleRoads(key,data){
  const[ti,tj]=key.split('_').map(Number),ox=ti*T,oz=tj*T;
  for(const r of data.r||[]){
    if(r[0]>11||(r[2]&4))continue;const a=r[3];
    for(let i=0;i+3<a.length;i+=4){
      const x0=a[i]/10+ox,z0=a[i+1]/10+oz,x1=a[i+2]/10+ox,z1=a[i+3]/10+oz;
      if(Math.hypot(x0-NJ.spawn[0],z0-NJ.spawn[1])<260)NJ.roadSample.push({x:(x0+x1)/2,z:(z0+z1)/2,h:Math.atan2(x1-x0,z1-z0)});
    }
  }
}
/* ---------- per-frame ---------- */
NJ.update=function(dt){NJ.dt=dt;
  if(!NJ.on)return;
  NJ.frame++;
  if(M.scene.fog&&M.scene.fog.far>=400)M.scene.fog.far=1800;
  waterMesh.position.x=M.P.x;waterMesh.position.z=M.P.z;
  if(NJ.frame%20===0)stream(M.P.x,M.P.z);
  trafficUpdate(Math.min(.1,NJ.dt||.033));
  if(NJ.frame%45===0)hideOld();
  {const dayF=M.dayF;const n=1-dayF;matLamp.color.setRGB(.35+n*.65,.35+n*.6,.35+n*.35);matGlow.opacity=n*.85;matSky.emissive.setRGB(n*.9,n*.85,.65*n);const hz=.55+.45*dayF;matSky.color.setRGB(.6*hz+.25,.68*hz+.25,.8*hz+.2);matBld.emissive.setRGB(n*1.0,n*.92,n*.7);matWater.color.setHex(0x2f6b99).multiplyScalar(.25+.75*dayF);}
};
})();
