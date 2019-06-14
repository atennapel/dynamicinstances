/////
const obj = a => {
  const o = {};
  for(let i = 0, l = a.length; i < l; i++)
    o[a[i][0]] = a[i][1];
  return o;
};
const err = m => { throw new Error(m) };

/////
let _id = 0;
const new_ = eff => {
  const id = _id++;
  return obj([['_id', id]].concat(eff.map(op => [op, `${id}.${op}`])));
};

const CONT = 'CONT';
const RET = 'RET';

const return_ = val => ({ tag: RET, val });
const cont = (op, val, cont) => ({ tag: CONT, op, val, cont });
const perform = (op, val) => cont(op, val, return_);
const pure = c => c.tag === RET? c.val: err('pure failed');

const do_ = (c, f) =>
  c.tag === RET? f(c.val):
  c.tag === CONT? cont(c.op, c.val, v => do_(c.cont(v), f)):
  err('impossible');

const handler = m => c => 
  c.tag === RET? (m['return']? m['return'](c.val): c):
  c.tag === CONT? (m[c.op]? m[c.op](c.val, v => handler(m)(c.cont(v))): cont(c.op, c.val, v => handler(m)(c.cont(v)))):
  err('impossible');
const phandler = m => iv => c => 
  c.tag === RET? (m['return']? m['return'](iv, c.val): c):
  c.tag === CONT? (m[c.op]? m[c.op](iv, c.val, (iv, v) => phandler(m)(iv)(c.cont(v))): cont(c.op, c.val, v => phandler(m)(iv)(c.cont(v)))):
  err('impossible');

/////
const Flip = ['flip'];
const State = ['get', 'put'];
const New = ['new'];

const Printf = ['show'];
const printf = i => handler({
  [i.show]: (f, k) => x => k(f(x)),
});

const Delim = ['shift'];
const delim = i => handler({
  [i.shift]: (f, k) => f(k),
});
const reset = (i, f) => delim(i)(f());

const flipHandler = i => handler({
  [i.flip]: (_, k) => k(true),
});
const state = i => phandler({
  [i.get]: (v, _, k) => k(v, v),
  [i.put]: (_, v, k) => k(v, null)
});

const newI = new_(New);
const newHandler = handler({
  [newI.new]: ([e, h, v], k) => {
    const i = new_(e);
    return h(i)(v)(k(i));
  }
});

const ref = v => perform(newI.new, [State, state, v]);

const myFlip = new_(Flip);
const myFlip2 = new_(Flip);

/*
  (\r ->
    v <- r#get;
    r#put (v + 1);
    v) : (i:Inst (State Num)) -> <i> Num
*/
const postInc = r =>
  do_(perform(r.get), v =>
  do_(perform(r.put, v + 1), _ =>
  return_(v)));

/*
  p =
    r <- ref 1;
    v <- postInc r;
    (v, r)
  p2 =
    (v, r) <- p;
    v' <- r#get;
    (v, v')
*/
const p =
  do_(ref(1), r =>
  do_(postInc(r), v =>
  return_([v, r])));
const p2 =
  do_(p, ([v, r]) =>
  do_(perform(r.get), v_ =>
  return_([v, v_])));

const show = new_(Printf);

const str = x => x;
const num = x => ''+x;
const arr = x => '['+x.join(', ')+']';

const pr =
  do_(perform(show.show, str), a =>
  do_(perform(show.show, arr), b =>
  return_("hey " + a + " " + b)));

const i = new_(Delim);
const reset_ = f => reset(i, f);
const shift_ = f => perform(i.shift, f);
const shifti = (i, f) => perform(i.shift, f);

const testdelim =
  reset(i, () => {
    const j = new_(Delim);
    return do_(shifti(i, k => k(2)), z => reset(j, () =>
      do_(shifti(j, k => k(z)), x => return_(x + 1))));
  });

const r1 = new_(State);
const testescape =
  state(r1)(1)(
    do_((() => {
      const r2 = new_(State);
      return perform(r1.put, r2);
    })(), () =>
    do_(perform(r1.get), inst =>
      perform(inst.get)))
  );

console.log(testescape);
