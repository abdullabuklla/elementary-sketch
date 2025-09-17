  /* ===================== Config ===================== */
    const X_MIN=-10,X_MAX=10,Y_MIN=-10,Y_MAX=10,SAMPLES=600;
    const SHIFT_STEP_X=0.2, SHIFT_STEP_Y=0.2, SCALE_STEP=1.04, HOLD_STEP_MS=55, ACC_THRESHOLD=0.99;

    /* Target generator limits (ops simulate the same user actions) */
    const GEN_MIN_OPS = 5;
    const GEN_MAX_OPS = 12;

    /* ===================== State ===================== */
    let paramsPlayer, paramsTarget, acc=0, won=false, brightness=0, particles=[];
    let snapAbs=null, snapNeg=null; // for exact undo on player

    /* ===================== Mapping ===================== */
    let scalePX=1,x0=0,y0=0; const MARGIN=40;
    function updateMapping(){
        const usableW=width-2*MARGIN, usableH=height-2*MARGIN;
        const sx=usableW/(X_MAX-X_MIN), sy=usableH/(Y_MAX-Y_MIN);
        scalePX=Math.min(sx,sy);
        const worldWpx=scalePX*(X_MAX-X_MIN), worldHpx=scalePX*(Y_MAX-Y_MIN);
        const left=(width-worldWpx)/2, top=(height-worldHpx)/2;
        x0=left - X_MIN*scalePX; y0=top + Y_MAX*scalePX;
    }
    const sx=(x)=>x0+x*scalePX, sy=(y)=>y0-y*scalePX;

    /* ===================== Helpers ===================== */
    const randBetween=(a,b)=>a+Math.random()*(b-a);
    const randInt=(a,b)=>Math.floor(a+Math.random()*(b-a+1));
    const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
    const snapToStep=(v,step)=>Math.round(v/step)*step;
    const approx=(v,t=1e-12)=>Math.abs(v)<t;
    function fmt(n,d=1){ let s=(approx(n)?0:+n.toFixed(d)).toString(); s=s.replace(/(\.\d*?[1-9])0+$/,'$1').replace(/\.0+$/,''); return s.replace(/-/g,'−');}
    const plusMinus=(n)=> (n>=0?" + ":" − ")+fmt(Math.abs(n));
    const deepClone=(o)=>JSON.parse(JSON.stringify(o));

    function stepScaleSigned(v, inc){ // inc: +1 or -1
        const EPS=1e-4, MAX=20;
        if (v===0) v=EPS;
        let sign = Math.sign(v)||1, mag=Math.max(EPS,Math.abs(v));
        if (inc*sign>0){ mag*=SCALE_STEP; } else { mag/=SCALE_STEP; if(mag<EPS){ sign*=-1; mag=EPS; } }
        v = sign*mag;
        if (v> MAX) v= MAX;
        if (v<-MAX) v=-MAX;
        return v;
    }

    /* ===================== Base funcs ===================== */
    function baseFunc(b,x){
        switch(b){
            case 1: return x;
            case 2: return x*x;
            case 3: return Math.exp(x)-1;
            case 4: return (x>0)?Math.log(x):NaN;
            default: return x;
        }
    }

    /* ===================== Model with ordered wrappers ===================== */
    // params: {a,b,h,Kin,Kout,base,wrapOrder:['abs'|'neg',...], dAbs, dNeg, negXActive}
    function applyParams(p,x){
        const xarg = p.negXActive ? -x : x;
        const z = p.b*(xarg - p.h);
        let v = baseFunc(p.base, z);
        if(!isFinite(v)) return NaN;
        v = p.a*v + (p.Kin||0);

        for(const w of (p.wrapOrder||[])){
            if(w==='abs') v = Math.abs(v + (p.dAbs||0));
            else if(w==='neg') v = -(v + (p.dNeg||0));
        }
        v += (p.Kout||0);
        return isFinite(v)? clamp(v, Y_MIN*3, Y_MAX*3) : NaN;
    }

    /* ===================== TeX ===================== */
    function innerAffine(p){
        const B = p.negXActive ? -p.b : p.b;
        const C = p.b*p.h; // z = B x - C
        const Bpart=approx(B-1)?"x":(approx(B+1)?"−x":`${fmt(B)}\\,x`);
        if(approx(C)) return Bpart;
        return `${Bpart} ${C>=0?"-":"+"} ${fmt(Math.abs(C))}`;
    }
    function slopeInterceptTex(m, b){
        const EPS = 1e-9;
        if (Math.abs(m) < EPS) return fmt(b); // y = constant
        let mTerm = "";
        if (approx(m-1))      mTerm = "x";
        else if (approx(m+1)) mTerm = "−x";
        else                  mTerm = `${fmt(m)}\\,x`;
        const bTerm = approx(b) ? "" : plusMinus(b);
        return `${mTerm}${bTerm}`;
    }
    function makeTeX(p){
        const z=innerAffine(p);
        const sPart=approx(p.a-1)? "" : `${fmt(p.a)}\\,`;

        // Pretty linear only when no wrappers
        if (p.base===1 && (!p.wrapOrder || p.wrapOrder.length===0)){
            const m = p.a * (p.negXActive ? -p.b : p.b);
            const c = (-p.a*p.b*p.h) + (p.Kin||0) + (p.Kout||0);
            return `y = ${slopeInterceptTex(m, c)}`;
        }

        // core
        let core;
        if(p.base===1) core = `${sPart}\\left(${z}\\right)`;
        else if(p.base===2) core = `${sPart}\\left(${z}\\right)^{2}`;
        else if(p.base===3) core = `${sPart}e^{\\left(${z}\\right)}`;
        else if(p.base===4) core = `${sPart}\\ln\\left(${z}\\right)`;
        else core = `${sPart}\\left(${z}\\right)`; // fallback, never "0"

        if(!approx(p.Kin||0)) core += ((p.Kin>=0)?" + ":" − ")+fmt(Math.abs(p.Kin));

        // wrappers in order
        let expr = core;
        for(const w of (p.wrapOrder||[])){
            if(w==='abs'){
                const d=p.dAbs||0;
                expr = approx(d) ? `\\left|${expr}\\right|`
                    : `\\left|${expr} ${d>=0?'+':'−'} ${fmt(Math.abs(d))}\\right|`;
            }else if(w==='neg'){
                const d=p.dNeg||0;
                expr = approx(d) ? `-\\left(${expr}\\right)`
                    : `-\\left(${expr} ${d>=0?'+':'−'} ${fmt(Math.abs(d))}\\right)`;
            }
        }
        return approx(p.Kout||0) ? `y = ${expr}` : `y = \\left(${expr}\\right)${plusMinus(p.Kout)}`;
    }
    function renderFormula(el, tex){
        if(!window.katex){ el.textContent = tex; return; }
        katex.render(tex, el, {throwOnError:false});
    }

    /* ===================== Init ===================== */
    function defaultParams(base){
        return { a:1, b:1, h:0, Kin:0, Kout:0, base, wrapOrder:[], dAbs:0, dNeg:0, negXActive:false };
    }
    function pickRandomBase(notEq){ const choices=[1,2,3,4].filter(v=>v!==notEq); return choices[Math.floor(Math.random()*choices.length)]; }
    function resetPlayer(randomBaseDifferentFromTarget=true){
        const base=(randomBaseDifferentFromTarget && paramsTarget)? pickRandomBase(paramsTarget.base) : [1,2,3,4][Math.floor(Math.random()*4)];
        paramsPlayer=defaultParams(base);
        snapAbs=null; snapNeg=null;
    }

    /* ===================== Target generator (simulate the same moves) ===================== */
    function genReachableTarget(){
        let p = defaultParams([1,2,3,4][randInt(0,3)]);

        const ops = randInt(GEN_MIN_OPS, GEN_MAX_OPS);
        for(let k=0;k<ops;k++){
            const r = Math.random();

            if(r < 0.14){                // move h
                const dir = Math.random()<0.5 ? -randInt(1,20) : randInt(1,20);
                p.h = snapToStep(p.h + dir*SHIFT_STEP_X, SHIFT_STEP_X);
            }else if(r < 0.28){          // move d (Kout)
                const dir = Math.random()<0.5 ? -randInt(1,20) : randInt(1,20);
                p.Kout = snapToStep(p.Kout + dir*SHIFT_STEP_Y, SHIFT_STEP_Y);
            }else if(r < 0.42){          // scale a
                const dir = Math.random()<0.5 ? -randInt(1,20) : randInt(1,20);
                p.a = stepScaleSigned(p.a, dir);
            }else if(r < 0.56){          // scale b
                const dir = Math.random()<0.5 ? -randInt(1,20) : randInt(1,20);
                p.b = stepScaleSigned(p.b, dir);
            }else if(r < 0.68){          // toggle A (wrap current)
                if(!p.wrapOrder.includes('abs')){ p.dAbs += p.Kout; p.Kout=0; p.wrapOrder.push('abs'); }
                else if(Math.random()<0.25){ // sometimes remove
                    // unwrap by reversing the absorption: push Kout back out
                    p.Kout += p.dAbs; p.dAbs=0;
                    p.wrapOrder = p.wrapOrder.filter(w=>w!=='abs');
                }
            }else if(r < 0.80){          // toggle N (wrap current)
                if(!p.wrapOrder.includes('neg')){ p.dNeg += p.Kout; p.Kout=0; p.wrapOrder.push('neg'); }
                else if(Math.random()<0.25){
                    p.Kout += p.dNeg; p.dNeg=0;
                    p.wrapOrder = p.wrapOrder.filter(w=>w!=='neg');
                }
            }else if(r < 0.90){          // mirror x
                p.negXActive = !p.negXActive;
            }else{                       // change base (and clear wrappers to mirror UI behavior)
                p.base = [1,2,3,4][randInt(0,3)];
                p.wrapOrder=[]; p.dAbs=0; p.dNeg=0; // same as UI base change
            }
        }
        return p;
    }

    function randomTarget(){
        paramsTarget = genReachableTarget();   // always reachable by the same moves
        resetPlayer(true); won=false; particles=[];
    }

    /* ===================== Accuracy ===================== */
    function computeAccuracy(){
        let se=0,n=0;
        for(let i=0;i<SAMPLES;i++){
            const x=X_MIN + (i/(SAMPLES-1))*(X_MAX-X_MIN);
            const gt=applyParams(paramsTarget,x), pr=applyParams(paramsPlayer,x);
            if(!isNaN(gt)&&!isNaN(pr)){ se+=(gt-pr)*(gt-pr); n++; }
        }
        if(n===0) return 0;
        const rmse=Math.sqrt(se/n);
        const denom=(Y_MAX - Y_MIN)/2; // stable normalization (handles constant lines)
        return Math.max(0, Math.min(1, 1 - rmse/denom));
    }

    /* ===================== Drawing ===================== */
    function drawAxesAndTicks(){
        stroke(36,36,36,160); strokeWeight(1);
        for(let gx=Math.ceil(X_MIN); gx<=Math.floor(X_MAX); gx++){ const X=sx(gx); line(X,sy(Y_MIN),X,sy(Y_MAX)); }
        for(let gy=Math.ceil(Y_MIN); gy<=Math.floor(Y_MAX); gy++){ const Y=sy(gy); line(sx(X_MIN),Y,sx(X_MAX),Y); }
        stroke(50,130,170,200); strokeWeight(1.5); line(sx(X_MIN),sy(0),sx(X_MAX),sy(0)); line(sx(0),sy(Y_MIN),sx(0),sy(Y_MAX));
        fill(200); noStroke(); textAlign(CENTER,TOP); textSize(12);
        for(let gx=Math.ceil(X_MIN); gx<=Math.floor(X_MAX); gx++){ const X=sx(gx); stroke(160); line(X,sy(0)-4,X,sy(0)+4); noStroke(); if(gx!==0) text(gx.toString(),X,sy(0)+6); }
        textAlign(LEFT,CENTER);
        for(let gy=Math.ceil(Y_MIN); gy<=Math.floor(Y_MAX); gy++){ const Y=sy(gy); stroke(160); line(sx(0)-4,Y,sx(0)+4,Y); noStroke(); if(gy!==0) text(gy.toString(),sx(0)+6,Y); }
    }
    function drawFunction(p,rgba,thick){
        noFill(); stroke(rgba[0],rgba[1],rgba[2],rgba[3]); strokeWeight(thick);
        beginShape(); let started=false;
        for(let i=0;i<SAMPLES;i++){
            const x=X_MIN + (i/(SAMPLES-1))*(X_MAX-X_MIN);
            const y=applyParams(p,x);
            if(isNaN(y)){ if(started){ endShape(); started=false; beginShape(); } continue; }
            vertex(sx(x),sy(y)); started=true;
        }
        endShape();
    }
    function celebrate(show100){
        if(particles.length<300){ for(let i=0;i<10;i++) particles.push({x:random(width),y:-10,vx:random(-1,1),vy:random(1,4),life:random(60,140),s:random(2,5)}); }
        noStroke();
        for(const p of particles){ fill(random(140,255),random(140,255),random(140,255),230); square(p.x,p.y,p.s); p.x+=p.vx; p.y+=p.vy; p.vy+=0.02; p.life-=1; }
        particles=particles.filter(p=>p.life>0&&p.y<height+20);
        textAlign(CENTER,CENTER); textSize(min(64,width*0.06)); fill(255); stroke(0,255,200); strokeWeight(2);
        text("You found the function! 🎉", width/2, height*0.16);
        if(show100){ textAlign(CENTER,CENTER); textSize(min(34,width*0.06)); fill(255); stroke(0,255,200); strokeWeight(2); text("You are 100% correct!", width/2, height*0.24); }
    }

    /* ===================== p5 lifecycle ===================== */
    function setup(){ createCanvas(window.innerWidth, window.innerHeight); updateMapping(); randomTarget(); setupUI(); textFont('system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial, sans-serif'); }
    function windowResized(){ resizeCanvas(window.innerWidth, window.innerHeight); updateMapping(); }

    /* ===================== Key-hold repeat ===================== */
    const held={left:false,right:false,up:false,down:false,shift:false}; let lastStepTime=0;
    function doStep(dx,dy,isScale){
        if(isScale){
            if(dx) paramsPlayer.b = stepScaleSigned(paramsPlayer.b, dx);  // Shift+←/→
            if(dy) paramsPlayer.a = stepScaleSigned(paramsPlayer.a, dy);  // Shift+↑/↓
        }else{
            paramsPlayer.h    = snapToStep(paramsPlayer.h - dx*SHIFT_STEP_X, SHIFT_STEP_X);
            paramsPlayer.Kout = snapToStep(paramsPlayer.Kout + dy*SHIFT_STEP_Y, SHIFT_STEP_Y);
        }
    }
    function processHeld(){
        const now=millis();
        if(now-lastStepTime>=HOLD_STEP_MS){
            let dx=0,dy=0; if(held.left)dx-=1; if(held.right)dx+=1; if(held.up)dy+=1; if(held.down)dy-=1;
            if(dx||dy){ doStep(dx,dy, held.shift||shiftHeldUI); lastStepTime=now; }
        }
    }

    /* ===================== Wrapper toggles (wrap CURRENT) ===================== */
    function isAbsOn(p){ return (p.wrapOrder||[]).includes('abs'); }
    function isNegOn(p){ return (p.wrapOrder||[]).includes('neg'); }

    function turnAbsOn(){
        if(isAbsOn(paramsPlayer)) return;
        snapAbs = deepClone(paramsPlayer);
        paramsPlayer.dAbs += (paramsPlayer.Kout||0);
        paramsPlayer.Kout  = 0;
        paramsPlayer.wrapOrder.push('abs');
    }
    function turnAbsOff(){
        if(snapAbs){ paramsPlayer = deepClone(snapAbs); snapAbs=null; }
        else paramsPlayer.wrapOrder = (paramsPlayer.wrapOrder||[]).filter(w=>w!=='abs');
    }
    function toggleAbs(){ isAbsOn(paramsPlayer) ? turnAbsOff() : turnAbsOn(); }

    function turnNegOn(){
        if(isNegOn(paramsPlayer)) return;
        snapNeg = deepClone(paramsPlayer);
        paramsPlayer.dNeg += (paramsPlayer.Kout||0);
        paramsPlayer.Kout  = 0;
        paramsPlayer.wrapOrder.push('neg');
    }
    function turnNegOff(){
        if(snapNeg){ paramsPlayer = deepClone(snapNeg); snapNeg=null; }
        else paramsPlayer.wrapOrder = (paramsPlayer.wrapOrder||[]).filter(w=>w!=='neg');
    }
    function toggleNeg(){ isNegOn(paramsPlayer) ? turnNegOff() : turnNegOn(); }

    function toggleMirrorX(){ paramsPlayer.negXActive = !paramsPlayer.negXActive; } // pure toggle

    /* ===================== Input ===================== */
    function keyPressed(){
        if(keyCode===LEFT_ARROW)  held.left=true;
        if(keyCode===RIGHT_ARROW) held.right=true;
        if(keyCode===UP_ARROW)    held.up=true;
        if(keyCode===DOWN_ARROW)  held.down=true;
        if(keyCode===SHIFT)       held.shift=true;

        if(key==='A'||key==='a') toggleAbs();
        if(key==='N'||key==='n') toggleNeg();
        if(key==='M'||key==='m') toggleMirrorX();
        if(key==='R'||key==='r') resetPlayer(true);
        if(key===' ')            randomTarget();

        if(key==='1'||key==='2'||key==='3'||key==='4'){
            const b=parseInt(key,10);
            paramsPlayer.base=b; paramsPlayer.wrapOrder=[]; paramsPlayer.dAbs=0; paramsPlayer.dNeg=0; paramsPlayer.negXActive=false; snapAbs=snapNeg=null;
        }
    }
    function keyReleased(){
        if(keyCode===LEFT_ARROW)  held.left=false;
        if(keyCode===RIGHT_ARROW) held.right=false;
        if(keyCode===UP_ARROW)    held.up=false;
        if(keyCode===DOWN_ARROW)  held.down=false;
        if(keyCode===SHIFT)       held.shift=false;
    }

    /* ===================== Frame ===================== */
    function updateButtonStates(){
        document.getElementById('btnA').classList.toggle('on', isAbsOn(paramsPlayer));
        document.getElementById('btnN').classList.toggle('on', isNegOn(paramsPlayer));
        document.getElementById('btnM').classList.toggle('on', paramsPlayer.negXActive);
    }
    function draw(){
        acc=computeAccuracy(); brightness=map(acc,0,1,0,90); background(brightness);
        processHeld(); drawAxesAndTicks();

        drawFunction(paramsTarget,[255, 80, 0, 170],2);                 // target
        const glow=map(acc,0,1,100,255); drawFunction(paramsPlayer,[0,255,255,glow],3); // player

        document.getElementById('accuracy').textContent=`Acc: ${(acc*100).toFixed(2)}%`;
        renderFormula(document.getElementById('playerFormula'), makeTeX(paramsPlayer));

        const tgtEl=document.getElementById('targetFormula');
        if(document.getElementById('chkShowTargetFormula').checked){
            tgtEl.style.display="block"; renderFormula(tgtEl, `\\text{Target:}\\; ${makeTeX(paramsTarget)}`);
        }else tgtEl.style.display="none";

        updateButtonStates();

        const ON  = ACC_THRESHOLD, OFF = Math.max(0, ACC_THRESHOLD - 0.02);
        if (!won && acc >= ON) won = true;
        else if (won && acc < OFF){ won = false; particles = []; }
        if(won) celebrate(acc>=1-1e-12);
    }

    /* ===================== UI ===================== */
    let shiftHeldUI=false;
    function setupUI(){
        const q=(id)=>document.getElementById(id);
        const flash=(el)=>{ el.style.transition='background .12s'; const old=el.style.background; el.style.background='#1f2a30'; setTimeout(()=>{el.style.background=old||'#111';},120); };

        const btnShift=q('btnShift'); btnShift.onclick=()=>{ shiftHeldUI=!shiftHeldUI; btnShift.classList.toggle('on',shiftHeldUI); };

        q('btnA').onclick = ()=>{ toggleAbs(); flash(q('btnA')); };
        q('btnN').onclick = ()=>{ toggleNeg(); flash(q('btnN')); };
        q('btnM').onclick = ()=>{ toggleMirrorX(); flash(q('btnM')); };
        q('btnR').onclick = ()=>{ resetPlayer(true); flash(q('btnR')); };
        q('btnSpace').onclick = ()=>{ randomTarget(); flash(q('btnSpace')); };

        q('btn1').onclick=()=>{ paramsPlayer.base=1; paramsPlayer.wrapOrder=[]; paramsPlayer.dAbs=0; paramsPlayer.dNeg=0; paramsPlayer.negXActive=false; snapAbs=snapNeg=null; flash(q('btn1')); };
        q('btn2').onclick=()=>{ paramsPlayer.base=2; paramsPlayer.wrapOrder=[]; paramsPlayer.dAbs=0; paramsPlayer.dNeg=0; paramsPlayer.negXActive=false; snapAbs=snapNeg=null; flash(q('btn2')); };
        q('btn3').onclick=()=>{ paramsPlayer.base=3; paramsPlayer.wrapOrder=[]; paramsPlayer.dAbs=0; paramsPlayer.dNeg=0; paramsPlayer.negXActive=false; snapAbs=snapNeg=null; flash(q('btn3')); };
        q('btn4').onclick=()=>{ paramsPlayer.base=4; paramsPlayer.wrapOrder=[]; paramsPlayer.dAbs=0; paramsPlayer.dNeg=0; paramsPlayer.negXActive=false; snapAbs=snapNeg=null; flash(q('btn4')); };

        function bindHold(btn, onStart, onEnd){
            let interval=null;
            btn.addEventListener('touchstart', e=>{ e.preventDefault(); onStart(); interval=setInterval(onStart,HOLD_STEP_MS); }, {passive:false});
            btn.addEventListener('touchend',   e=>{ e.preventDefault(); if(interval){clearInterval(interval);interval=null;} onEnd&&onEnd(); }, {passive:false});
            btn.addEventListener('mousedown', ()=>{ onStart(); interval=setInterval(onStart,HOLD_STEP_MS); });
            btn.addEventListener('mouseup',   ()=>{ if(interval){clearInterval(interval);interval=null;} onEnd&&onEnd(); });
            btn.addEventListener('mouseleave',()=>{ if(interval){clearInterval(interval);interval=null;} onEnd&&onEnd(); });
        }
        bindHold(q('btnLeft'),  ()=>{ doStep(-1,0,shiftHeldUI); flash(q('btnLeft')); });
        bindHold(q('btnRight'), ()=>{ doStep( 1,0,shiftHeldUI); flash(q('btnRight')); });
        bindHold(q('btnUp'),    ()=>{ doStep( 0,1,shiftHeldUI); flash(q('btnUp')); });
        bindHold(q('btnDown'),  ()=>{ doStep( 0,-1,shiftHeldUI); flash(q('btnDown')); });

        const chk=q('chkShowTargetFormula'); chk.checked=false;
    }
