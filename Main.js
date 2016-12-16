"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0="deltaZ",_1="deltaY",_2="deltaX",_3=function(_4,_5){var _6=E(_4);return (_6._==0)?E(_5):new T2(1,_6.a,new T(function(){return B(_3(_6.b,_5));}));},_7=function(_8,_9){var _a=jsShowI(_8);return new F(function(){return _3(fromJSStr(_a),_9);});},_b=41,_c=40,_d=function(_e,_f,_g){if(_f>=0){return new F(function(){return _7(_f,_g);});}else{if(_e<=6){return new F(function(){return _7(_f,_g);});}else{return new T2(1,_c,new T(function(){var _h=jsShowI(_f);return B(_3(fromJSStr(_h),new T2(1,_b,_g)));}));}}},_i=new T(function(){return B(unCStr(")"));}),_j=new T(function(){return B(_d(0,2,_i));}),_k=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_j));}),_l=function(_m){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_d(0,_m,_k));}))));});},_n=function(_o,_){return new T(function(){var _p=Number(E(_o)),_q=jsTrunc(_p);if(_q<0){return B(_l(_q));}else{if(_q>2){return B(_l(_q));}else{return _q;}}});},_r=0,_s=new T3(0,_r,_r,_r),_t="button",_u=new T(function(){return eval("jsGetMouseCoords");}),_v=__Z,_w=function(_x,_){var _y=E(_x);if(!_y._){return _v;}else{var _z=B(_w(_y.b,_));return new T2(1,new T(function(){var _A=Number(E(_y.a));return jsTrunc(_A);}),_z);}},_B=function(_C,_){var _D=__arr2lst(0,_C);return new F(function(){return _w(_D,_);});},_E=function(_F,_){return new F(function(){return _B(E(_F),_);});},_G=function(_H,_){return new T(function(){var _I=Number(E(_H));return jsTrunc(_I);});},_J=new T2(0,_G,_E),_K=function(_L,_){var _M=E(_L);if(!_M._){return _v;}else{var _N=B(_K(_M.b,_));return new T2(1,_M.a,_N);}},_O=new T(function(){return B(unCStr("base"));}),_P=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Q=new T(function(){return B(unCStr("IOException"));}),_R=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_O,_P,_Q),_S=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_R,_v,_v),_T=function(_U){return E(_S);},_V=function(_W){return E(E(_W).a);},_X=function(_Y,_Z,_10){var _11=B(A1(_Y,_)),_12=B(A1(_Z,_)),_13=hs_eqWord64(_11.a,_12.a);if(!_13){return __Z;}else{var _14=hs_eqWord64(_11.b,_12.b);return (!_14)?__Z:new T1(1,_10);}},_15=function(_16){var _17=E(_16);return new F(function(){return _X(B(_V(_17.a)),_T,_17.b);});},_18=new T(function(){return B(unCStr(": "));}),_19=new T(function(){return B(unCStr(")"));}),_1a=new T(function(){return B(unCStr(" ("));}),_1b=new T(function(){return B(unCStr("interrupted"));}),_1c=new T(function(){return B(unCStr("system error"));}),_1d=new T(function(){return B(unCStr("unsatisified constraints"));}),_1e=new T(function(){return B(unCStr("user error"));}),_1f=new T(function(){return B(unCStr("permission denied"));}),_1g=new T(function(){return B(unCStr("illegal operation"));}),_1h=new T(function(){return B(unCStr("end of file"));}),_1i=new T(function(){return B(unCStr("resource exhausted"));}),_1j=new T(function(){return B(unCStr("resource busy"));}),_1k=new T(function(){return B(unCStr("does not exist"));}),_1l=new T(function(){return B(unCStr("already exists"));}),_1m=new T(function(){return B(unCStr("resource vanished"));}),_1n=new T(function(){return B(unCStr("timeout"));}),_1o=new T(function(){return B(unCStr("unsupported operation"));}),_1p=new T(function(){return B(unCStr("hardware fault"));}),_1q=new T(function(){return B(unCStr("inappropriate type"));}),_1r=new T(function(){return B(unCStr("invalid argument"));}),_1s=new T(function(){return B(unCStr("failed"));}),_1t=new T(function(){return B(unCStr("protocol error"));}),_1u=function(_1v,_1w){switch(E(_1v)){case 0:return new F(function(){return _3(_1l,_1w);});break;case 1:return new F(function(){return _3(_1k,_1w);});break;case 2:return new F(function(){return _3(_1j,_1w);});break;case 3:return new F(function(){return _3(_1i,_1w);});break;case 4:return new F(function(){return _3(_1h,_1w);});break;case 5:return new F(function(){return _3(_1g,_1w);});break;case 6:return new F(function(){return _3(_1f,_1w);});break;case 7:return new F(function(){return _3(_1e,_1w);});break;case 8:return new F(function(){return _3(_1d,_1w);});break;case 9:return new F(function(){return _3(_1c,_1w);});break;case 10:return new F(function(){return _3(_1t,_1w);});break;case 11:return new F(function(){return _3(_1s,_1w);});break;case 12:return new F(function(){return _3(_1r,_1w);});break;case 13:return new F(function(){return _3(_1q,_1w);});break;case 14:return new F(function(){return _3(_1p,_1w);});break;case 15:return new F(function(){return _3(_1o,_1w);});break;case 16:return new F(function(){return _3(_1n,_1w);});break;case 17:return new F(function(){return _3(_1m,_1w);});break;default:return new F(function(){return _3(_1b,_1w);});}},_1x=new T(function(){return B(unCStr("}"));}),_1y=new T(function(){return B(unCStr("{handle: "));}),_1z=function(_1A,_1B,_1C,_1D,_1E,_1F){var _1G=new T(function(){var _1H=new T(function(){var _1I=new T(function(){var _1J=E(_1D);if(!_1J._){return E(_1F);}else{var _1K=new T(function(){return B(_3(_1J,new T(function(){return B(_3(_19,_1F));},1)));},1);return B(_3(_1a,_1K));}},1);return B(_1u(_1B,_1I));}),_1L=E(_1C);if(!_1L._){return E(_1H);}else{return B(_3(_1L,new T(function(){return B(_3(_18,_1H));},1)));}}),_1M=E(_1E);if(!_1M._){var _1N=E(_1A);if(!_1N._){return E(_1G);}else{var _1O=E(_1N.a);if(!_1O._){var _1P=new T(function(){var _1Q=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1Q));},1);return new F(function(){return _3(_1y,_1P);});}else{var _1R=new T(function(){var _1S=new T(function(){return B(_3(_1x,new T(function(){return B(_3(_18,_1G));},1)));},1);return B(_3(_1O.a,_1S));},1);return new F(function(){return _3(_1y,_1R);});}}}else{return new F(function(){return _3(_1M.a,new T(function(){return B(_3(_18,_1G));},1));});}},_1T=function(_1U){var _1V=E(_1U);return new F(function(){return _1z(_1V.a,_1V.b,_1V.c,_1V.d,_1V.f,_v);});},_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);return new F(function(){return _1z(_20.a,_20.b,_20.c,_20.d,_20.f,_1Z);});},_21=function(_22,_23){var _24=E(_22);return new F(function(){return _1z(_24.a,_24.b,_24.c,_24.d,_24.f,_23);});},_25=44,_26=93,_27=91,_28=function(_29,_2a,_2b){var _2c=E(_2a);if(!_2c._){return new F(function(){return unAppCStr("[]",_2b);});}else{var _2d=new T(function(){var _2e=new T(function(){var _2f=function(_2g){var _2h=E(_2g);if(!_2h._){return E(new T2(1,_26,_2b));}else{var _2i=new T(function(){return B(A2(_29,_2h.a,new T(function(){return B(_2f(_2h.b));})));});return new T2(1,_25,_2i);}};return B(_2f(_2c.b));});return B(A2(_29,_2c.a,_2e));});return new T2(1,_27,_2d);}},_2j=function(_2k,_2l){return new F(function(){return _28(_21,_2k,_2l);});},_2m=new T3(0,_1W,_1T,_2j),_2n=new T(function(){return new T5(0,_T,_2m,_2o,_15,_1T);}),_2o=function(_2p){return new T2(0,_2n,_2p);},_2q=__Z,_2r=7,_2s=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_2t=new T6(0,_2q,_2r,_v,_2s,_2q,_2q),_2u=new T(function(){return B(_2o(_2t));}),_2v=function(_){return new F(function(){return die(_2u);});},_2w=function(_2x){return E(E(_2x).a);},_2y=function(_2z,_2A,_2B,_){var _2C=__arr2lst(0,_2B),_2D=B(_K(_2C,_)),_2E=E(_2D);if(!_2E._){return new F(function(){return _2v(_);});}else{var _2F=E(_2E.b);if(!_2F._){return new F(function(){return _2v(_);});}else{if(!E(_2F.b)._){var _2G=B(A3(_2w,_2z,_2E.a,_)),_2H=B(A3(_2w,_2A,_2F.a,_));return new T2(0,_2G,_2H);}else{return new F(function(){return _2v(_);});}}}},_2I=function(_){return new F(function(){return __jsNull();});},_2J=function(_2K){var _2L=B(A1(_2K,_));return E(_2L);},_2M=new T(function(){return B(_2J(_2I));}),_2N=new T(function(){return E(_2M);}),_2O=function(_2P,_2Q,_){if(E(_2P)==7){var _2R=__app1(E(_u),_2Q),_2S=B(_2y(_J,_J,_2R,_)),_2T=__get(_2Q,E(_2)),_2U=__get(_2Q,E(_1)),_2V=__get(_2Q,E(_0));return new T(function(){return new T3(0,E(_2S),E(_2q),E(new T3(0,_2T,_2U,_2V)));});}else{var _2W=__app1(E(_u),_2Q),_2X=B(_2y(_J,_J,_2W,_)),_2Y=__get(_2Q,E(_t)),_2Z=__eq(_2Y,E(_2N));if(!E(_2Z)){var _30=B(_n(_2Y,_));return new T(function(){return new T3(0,E(_2X),E(new T1(1,_30)),E(_s));});}else{return new T(function(){return new T3(0,E(_2X),E(_2q),E(_s));});}}},_31=function(_32,_33,_){return new F(function(){return _2O(_32,E(_33),_);});},_34="mouseout",_35="mouseover",_36="mousemove",_37="mouseup",_38="mousedown",_39="dblclick",_3a="click",_3b="wheel",_3c=function(_3d){switch(E(_3d)){case 0:return E(_3a);case 1:return E(_39);case 2:return E(_38);case 3:return E(_37);case 4:return E(_36);case 5:return E(_35);case 6:return E(_34);default:return E(_3b);}},_3e=new T2(0,_3c,_31),_3f=function(_3g,_){return new T1(1,_3g);},_3h=function(_3i){return E(_3i);},_3j=new T2(0,_3h,_3f),_3k=function(_3l,_3m,_){var _3n=B(A1(_3l,_)),_3o=B(A1(_3m,_));return _3n;},_3p=function(_3q,_3r,_){var _3s=B(A1(_3q,_)),_3t=B(A1(_3r,_));return new T(function(){return B(A1(_3s,_3t));});},_3u=function(_3v,_3w,_){var _3x=B(A1(_3w,_));return _3v;},_3y=function(_3z,_3A,_){var _3B=B(A1(_3A,_));return new T(function(){return B(A1(_3z,_3B));});},_3C=new T2(0,_3y,_3u),_3D=function(_3E,_){return _3E;},_3F=function(_3G,_3H,_){var _3I=B(A1(_3G,_));return new F(function(){return A1(_3H,_);});},_3J=new T5(0,_3C,_3D,_3p,_3F,_3k),_3K=new T(function(){return E(_2n);}),_3L=function(_3M){return E(E(_3M).c);},_3N=function(_3O){return new T6(0,_2q,_2r,_v,_3O,_2q,_2q);},_3P=function(_3Q,_){var _3R=new T(function(){return B(A2(_3L,_3K,new T(function(){return B(A1(_3N,_3Q));})));});return new F(function(){return die(_3R);});},_3S=function(_3T,_){return new F(function(){return _3P(_3T,_);});},_3U=function(_3V){return new F(function(){return A1(_3S,_3V);});},_3W=function(_3X,_3Y,_){var _3Z=B(A1(_3X,_));return new F(function(){return A2(_3Y,_3Z,_);});},_40=new T5(0,_3J,_3W,_3F,_3D,_3U),_41=new T2(0,_40,_3h),_42=new T2(0,_41,_3D),_43=0,_44=0,_45=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_46=function(_47){return E(E(_47).b);},_48=function(_49,_4a){var _4b=function(_){var _4c=__app1(E(_45),E(_4a)),_4d=__eq(_4c,E(_2N));return (E(_4d)==0)?new T1(1,_4c):_2q;};return new F(function(){return A2(_46,_49,_4b);});},_4e=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:32:24-33"));}),_4f=new T6(0,_2q,_2r,_v,_4e,_2q,_2q),_4g=new T(function(){return B(_2o(_4f));}),_4h=function(_){return _43;},_4i=new T(function(){return eval("alert");}),_4j=function(_4k,_4l){var _4m=function(_){var _4n=__app1(E(_4i),toJSStr(E(_4l)));return new F(function(){return _4h(_);});};return new F(function(){return A2(_46,_4k,_4m);});},_4o=new T(function(){return B(unCStr("Please complete the board"));}),_4p=new T(function(){return B(unCStr("Good job!"));}),_4q=new T(function(){return B(unCStr("Wrong Answer!"));}),_4r=function(_4s,_4t){if(_4s<=_4t){var _4u=function(_4v){return new T2(1,_4v,new T(function(){if(_4v!=_4t){return B(_4u(_4v+1|0));}else{return __Z;}}));};return new F(function(){return _4u(_4s);});}else{return __Z;}},_4w=new T(function(){return B(_4r(1,81));}),_4x=function(_4y,_4z){var _4A=E(_4z);if(!_4A._){return new T2(0,_v,_v);}else{var _4B=_4A.a,_4C=_4A.b,_4D=E(_4y);if(_4D==1){return new T2(0,new T2(1,_4B,_v),_4C);}else{var _4E=new T(function(){var _4F=B(_4x(_4D-1|0,_4C));return new T2(0,_4F.a,_4F.b);});return new T2(0,new T2(1,_4B,new T(function(){return E(E(_4E).a);})),new T(function(){return E(E(_4E).b);}));}}},_4G=function(_4H,_4I){var _4J=E(_4I);if(!_4J._){return __Z;}else{var _4K=new T(function(){if(_4H>0){var _4L=B(_4x(_4H,_4J));return new T2(0,_4L.a,_4L.b);}else{return new T2(0,_v,_4J);}});return new T2(1,new T(function(){return E(E(_4K).a);}),new T(function(){return B(_4G(_4H,E(_4K).b));}));}},_4M=new T(function(){return B(_4G(9,_4w));}),_4N=function(_4O){return E(E(_4O).a);},_4P=function(_4Q){return E(E(_4Q).b);},_4R=function(_4S){return new F(function(){return fromJSStr(E(_4S));});},_4T=function(_4U){return E(E(_4U).a);},_4V=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_4W=function(_4X,_4Y,_4Z,_50){var _51=new T(function(){var _52=function(_){var _53=__app2(E(_4V),B(A2(_4T,_4X,_4Z)),E(_50));return new T(function(){return String(_53);});};return E(_52);});return new F(function(){return A2(_46,_4Y,_51);});},_54=function(_55){return E(E(_55).d);},_56=function(_57,_58,_59,_5a){var _5b=B(_4N(_58)),_5c=new T(function(){return B(_54(_5b));}),_5d=function(_5e){return new F(function(){return A1(_5c,new T(function(){return B(_4R(_5e));}));});},_5f=new T(function(){return B(_4W(_57,_58,_59,new T(function(){return toJSStr(E(_5a));},1)));});return new F(function(){return A3(_4P,_5b,_5f,_5d);});},_5g=new T(function(){return B(unCStr("value"));}),_5h=46,_5i=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:118:17-22"));}),_5j=new T6(0,_2q,_2r,_v,_5i,_2q,_2q),_5k=new T(function(){return B(_2o(_5j));}),_5l=function(_5m,_){var _5n=E(_5m);if(!_5n._){return _v;}else{var _5o=_5n.b,_5p=new T(function(){return toJSStr(B(unAppCStr("i",new T(function(){return B(_d(0,E(_5n.a),_v));}))));},1),_5q=B(A3(_48,_41,_5p,_)),_5r=E(_5q);if(!_5r._){return new F(function(){return die(_5k);});}else{var _5s=B(A(_56,[_3j,_41,_5r.a,_5g,_])),_5t=E(_5s);if(!_5t._){var _5u=B(_5l(_5o,_));return new T2(1,_5h,_5u);}else{var _5v=B(_5l(_5o,_));return new T2(1,_5t.a,_5v);}}}},_5w=function(_5x,_){var _5y=E(_5x);if(!_5y._){return _v;}else{var _5z=B(_5l(_5y.a,_)),_5A=B(_5w(_5y.b,_));return new T2(1,_5z,_5A);}},_5B=function(_5C){while(1){var _5D=E(_5C);if(!_5D._){return false;}else{if(E(_5D.a)==46){return true;}else{_5C=_5D.b;continue;}}}},_5E=function(_5F){while(1){var _5G=E(_5F);if(!_5G._){return false;}else{if(!B(_5B(_5G.a))){_5F=_5G.b;continue;}else{return true;}}}},_5H=3,_5I=function(_5J,_5K){while(1){var _5L=E(_5K);if(!_5L._){return __Z;}else{var _5M=_5L.b,_5N=E(_5J);if(_5N==1){return E(_5M);}else{_5J=_5N-1|0;_5K=_5M;continue;}}}},_5O=function(_5P,_5Q){var _5R=E(_5Q);if(!_5R._){return __Z;}else{var _5S=_5R.a,_5T=E(_5P);return (_5T==1)?new T2(1,_5S,_v):new T2(1,_5S,new T(function(){return B(_5O(_5T-1|0,_5R.b));}));}},_5U=function(_5V,_5W){var _5X=E(_5W);return (_5X._==0)?__Z:new T2(1,new T(function(){var _5Y=E(_5V);if(0>=_5Y){return __Z;}else{return B(_5O(_5Y,_5X));}}),new T(function(){var _5Z=E(_5V);if(_5Z>0){return B(_5U(_5Z,B(_5I(_5Z,_5X))));}else{return B(_5U(_5Z,_5X));}}));},_60=function(_61,_62){var _63=E(_62);return (_63._==0)?__Z:new T2(1,new T(function(){return B(A1(_61,_63.a));}),new T(function(){return B(_60(_61,_63.b));}));},_64=function(_65){var _66=E(_65);if(!_66._){return __Z;}else{return new F(function(){return _3(_66.a,new T(function(){return B(_64(_66.b));},1));});}},_67=function(_68){return new F(function(){return _64(_68);});},_69=function(_6a){var _6b=E(_6a);if(!_6b._){return __Z;}else{var _6c=new T(function(){return B(_69(_6b.b));}),_6d=function(_6e){var _6f=E(_6e);return (_6f._==0)?E(_6c):new T2(1,new T(function(){return B(_67(_6f.a));}),new T(function(){return B(_6d(_6f.b));}));};return new F(function(){return _6d(_6b.a);});}},_6g=function(_6h){return new F(function(){return _5U(_5H,_6h);});},_6i=function(_6j){while(1){var _6k=B((function(_6l){var _6m=E(_6l);if(!_6m._){return __Z;}else{var _6n=_6m.b,_6o=E(_6m.a);if(!_6o._){_6j=_6n;return __continue;}else{return new T2(1,_6o.b,new T(function(){return B(_6i(_6n));}));}}})(_6j));if(_6k!=__continue){return _6k;}}},_6p=function(_6q){while(1){var _6r=B((function(_6s){var _6t=E(_6s);if(!_6t._){return __Z;}else{var _6u=_6t.b,_6v=E(_6t.a);if(!_6v._){_6q=_6u;return __continue;}else{return new T2(1,_6v.a,new T(function(){return B(_6p(_6u));}));}}})(_6q));if(_6r!=__continue){return _6r;}}},_6w=function(_6x){while(1){var _6y=B((function(_6z){var _6A=E(_6z);if(!_6A._){return __Z;}else{var _6B=_6A.b,_6C=E(_6A.a);if(!_6C._){_6x=_6B;return __continue;}else{var _6D=new T(function(){return B(_6w(new T2(1,_6C.b,new T(function(){return B(_6i(_6B));}))));});return new T2(1,new T2(1,_6C.a,new T(function(){return B(_6p(_6B));})),_6D);}}})(_6x));if(_6y!=__continue){return _6y;}}},_6E=function(_6F,_6G){return E(_6F)!=E(_6G);},_6H=function(_6I,_6J){return E(_6I)==E(_6J);},_6K=new T2(0,_6H,_6E),_6L=function(_6M){return E(E(_6M).a);},_6N=function(_6O,_6P,_6Q){while(1){var _6R=E(_6Q);if(!_6R._){return false;}else{if(!B(A3(_6L,_6O,_6P,_6R.a))){_6Q=_6R.b;continue;}else{return true;}}}},_6S=function(_6T){while(1){var _6U=E(_6T);if(!_6U._){return true;}else{var _6V=_6U.b;if(!B(_6N(_6K,_6U.a,_6V))){_6T=_6V;continue;}else{return false;}}}},_6W=function(_6X){while(1){var _6Y=E(_6X);if(!_6Y._){return true;}else{if(!B(_6S(_6Y.a))){return false;}else{_6X=_6Y.b;continue;}}}},_6Z=function(_70){while(1){var _71=E(_70);if(!_71._){return true;}else{if(!B(_6S(_71.a))){return false;}else{_70=_71.b;continue;}}}},_72=function(_73){while(1){var _74=E(_73);if(!_74._){return true;}else{if(!B(_6S(_74.a))){return false;}else{_73=_74.b;continue;}}}},_75=function(_76){if(!B(_72(_76))){return false;}else{if(!B(_6Z(B(_6w(_76))))){return false;}else{return new F(function(){return _6W(B(_69(B(_60(_6w,B(_5U(_5H,B(_60(_6g,_76)))))))));});}}},_77=function(_78,_){var _79=B(_5w(_4M,_));if(!B(_5E(_79))){if(!B(_75(_79))){var _7a=B(A3(_4j,_41,_4q,_));return _43;}else{var _7b=B(A3(_4j,_41,_4p,_));return _43;}}else{var _7c=B(A3(_4j,_41,_4o,_));return _43;}},_7d="check",_7e=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:31:24-33"));}),_7f=new T6(0,_2q,_2r,_v,_7e,_2q,_2q),_7g=new T(function(){return B(_2o(_7f));}),_7h="solve",_7i=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:30:24-36"));}),_7j=new T6(0,_2q,_2r,_v,_7i,_2q,_2q),_7k=new T(function(){return B(_2o(_7j));}),_7l="selector",_7m=new T(function(){return B(unCStr("!!: negative index"));}),_7n=new T(function(){return B(unCStr("Prelude."));}),_7o=new T(function(){return B(_3(_7n,_7m));}),_7p=new T(function(){return B(err(_7o));}),_7q=new T(function(){return B(unCStr("!!: index too large"));}),_7r=new T(function(){return B(_3(_7n,_7q));}),_7s=new T(function(){return B(err(_7r));}),_7t=function(_7u,_7v){while(1){var _7w=E(_7u);if(!_7w._){return E(_7s);}else{var _7x=E(_7v);if(!_7x){return E(_7w.a);}else{_7u=_7w.b;_7v=_7x-1|0;continue;}}}},_7y=function(_7z,_7A){if(_7A>=0){return new F(function(){return _7t(_7z,_7A);});}else{return E(_7p);}},_7B=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_7C=new T(function(){return eval("(function(e){while(e.firstChild){e.removeChild(e.firstChild);}})");}),_7D=new T(function(){return eval("(function(c,p){p.removeChild(c);})");}),_7E=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_7F=new T(function(){return B(unCStr("Reset"));}),_7G=new T(function(){return B(unCStr("btn-default"));}),_7H=new T(function(){return B(unCStr("btn"));}),_7I="controls",_7J=new T(function(){return B(_48(_41,_7I));}),_7K=function(_7L){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_d(9,_7L,_v));}))));});},_7M=function(_7N){var _7O=u_towlower(E(_7N));if(_7O>>>0>1114111){return new F(function(){return _7K(_7O);});}else{return _7O;}},_7P=new T(function(){return toJSStr(B(_60(_7M,_7F)));}),_7Q=new T(function(){return B(_48(_41,_7P));}),_7R=new T(function(){return B(_60(_7M,_7F));}),_7S=new T(function(){return B(unCStr("button"));}),_7T=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:72:49-61"));}),_7U=new T6(0,_2q,_2r,_v,_7T,_2q,_2q),_7V=new T(function(){return B(_2o(_7U));}),_7W=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:63:32-42"));}),_7X=new T6(0,_2q,_2r,_v,_7W,_2q,_2q),_7Y=new T(function(){return B(_2o(_7X));}),_7Z=new T(function(){return B(unCStr("id"));}),_80=function(_81,_82){if(_81<=0){if(_81>=0){return new F(function(){return quot(_81,_82);});}else{if(_82<=0){return new F(function(){return quot(_81,_82);});}else{return quot(_81+1|0,_82)-1|0;}}}else{if(_82>=0){if(_81>=0){return new F(function(){return quot(_81,_82);});}else{if(_82<=0){return new F(function(){return quot(_81,_82);});}else{return quot(_81+1|0,_82)-1|0;}}}else{return quot(_81-1|0,_82)-1|0;}}},_83=function(_84){var _85=E(_84);if(!_85._){return __Z;}else{return new F(function(){return _3(_85.a,new T(function(){return B(_83(_85.b));},1));});}},_86=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_87=new T(function(){return B(unCStr("1"));}),_88=new T(function(){return B(unCStr("onkeypress"));}),_89=new T(function(){return B(unCStr("return event.charCode >= 48 && event.charCode <= 57"));}),_8a=new T(function(){return B(unCStr("className"));}),_8b=new T(function(){return B(unCStr(" "));}),_8c=new T(function(){return B(unCStr("r"));}),_8d=new T(function(){return B(unCStr("cell"));}),_8e=new T(function(){return B(unCStr("d"));}),_8f=new T2(1,_8e,_v),_8g=new T(function(){return B(unCStr("td"));}),_8h=new T(function(){return B(unCStr("input"));}),_8i=new T(function(){return B(unCStr("tr"));}),_8j=new T(function(){return B(unCStr("maxlength"));}),_8k=function(_8l,_8m){var _8n=_8l%_8m;if(_8l<=0){if(_8l>=0){return E(_8n);}else{if(_8m<=0){return E(_8n);}else{var _8o=E(_8n);return (_8o==0)?0:_8o+_8m|0;}}}else{if(_8m>=0){if(_8l>=0){return E(_8n);}else{if(_8m<=0){return E(_8n);}else{var _8p=E(_8n);return (_8p==0)?0:_8p+_8m|0;}}}else{var _8q=E(_8n);return (_8q==0)?0:_8q+_8m|0;}}},_8r=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_8s=function(_8t,_8u){var _8v=E(_8u);return (_8v._==0)?__Z:new T2(1,_8t,new T2(1,_8v.a,new T(function(){return B(_8s(_8t,_8v.b));})));},_8w=function(_8x,_8y,_){var _8z=function(_8A,_8B,_){while(1){var _8C=B((function(_8D,_8E,_){var _8F=E(_8D);if(!_8F._){return _43;}else{var _8G=E(_8E);if(!_8G._){return _43;}else{var _8H=E(_8r),_8I=__app1(_8H,toJSStr(E(_8i))),_8J=_8I,_8K=function(_8L,_8M,_){while(1){var _8N=B((function(_8O,_8P,_){var _8Q=E(_8O);if(!_8Q._){return _43;}else{var _8R=_8Q.a,_8S=_8Q.b,_8T=E(_8P);if(!_8T._){return _43;}else{var _8U=_8T.b,_8V=__app1(_8H,toJSStr(E(_8h))),_8W=_8V,_8X=__app1(_8H,toJSStr(E(_8g))),_8Y=_8X,_8Z=E(_7E),_90=__app3(_8Z,_8W,toJSStr(E(_7Z)),toJSStr(B(unAppCStr("i",new T(function(){return B(_d(0,E(_8R),_v));}))))),_91=E(_8T.a),_92=function(_93,_){var _94=__app3(_8Z,_8W,toJSStr(E(_5g)),toJSStr(_93));return new F(function(){return _4h(_);});},_95=function(_){var _96=E(_86),_97=__app3(_96,_8W,toJSStr(E(_8j)),toJSStr(E(_87))),_98=__app3(_96,_8W,toJSStr(E(_88)),toJSStr(E(_89))),_99=new T(function(){var _9a=E(_8R),_9b=B(_8k(_9a-1|0,9))+1|0,_9c=new T(function(){var _9d=B(_80(_9a-1|0,9))+1|0;if(_9d>=9){return __Z;}else{if(!B(_8k(_9d,3))){return E(_8f);}else{return __Z;}}});if(_9b>=9){return B(_8s(_8b,_9c));}else{if(!B(_8k(_9b,3))){return B(_8s(_8b,new T2(1,_8c,_9c)));}else{return B(_8s(_8b,_9c));}}}),_9e=__app3(_8Z,_8Y,toJSStr(E(_8a)),toJSStr(B(_83(new T2(1,_8d,_99))))),_9f=E(_7B),_9g=__app2(_9f,_8W,_8Y),_9h=__app2(_9f,_8Y,_8J);return new F(function(){return _4h(_);});};if(E(_91)==46){var _9i=B(_92(_v,_)),_9j=B(_95(_));_8L=_8S;_8M=_8U;return __continue;}else{var _9k=B(_92(new T2(1,_91,_v),_)),_9l=B(_95(_));_8L=_8S;_8M=_8U;return __continue;}}}})(_8L,_8M,_));if(_8N!=__continue){return _8N;}}},_9m=B(_8K(_8F.a,_8G.a,_)),_9n=__app2(E(_7B),_8J,E(_8x));_8A=_8F.b;_8B=_8G.b;return __continue;}}})(_8A,_8B,_));if(_8C!=__continue){return _8C;}}};return new F(function(){return _8z(_4M,_8y,_);});},_9o="puzzle",_9p=new T(function(){return B(_48(_41,_9o));}),_9q=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_9r=function(_9s){return E(E(_9s).a);},_9t=function(_9u){return E(E(_9u).b);},_9v=function(_9w){return E(E(_9w).a);},_9x=function(_){return new F(function(){return nMV(_2q);});},_9y=new T(function(){return B(_2J(_9x));}),_9z=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_9A=function(_9B){return E(E(_9B).b);},_9C=function(_9D,_9E,_9F,_9G,_9H,_9I){var _9J=B(_9r(_9D)),_9K=B(_4N(_9J)),_9L=new T(function(){return B(_46(_9J));}),_9M=new T(function(){return B(_54(_9K));}),_9N=new T(function(){return B(A2(_4T,_9E,_9G));}),_9O=new T(function(){return B(A2(_9v,_9F,_9H));}),_9P=function(_9Q){return new F(function(){return A1(_9M,new T3(0,_9O,_9N,_9Q));});},_9R=function(_9S){var _9T=new T(function(){var _9U=new T(function(){var _9V=__createJSFunc(2,function(_9W,_){var _9X=B(A2(E(_9S),_9W,_));return _2N;}),_9Y=_9V;return function(_){return new F(function(){return __app3(E(_9z),E(_9N),E(_9O),_9Y);});};});return B(A1(_9L,_9U));});return new F(function(){return A3(_4P,_9K,_9T,_9P);});},_9Z=new T(function(){var _a0=new T(function(){return B(_46(_9J));}),_a1=function(_a2){var _a3=new T(function(){return B(A1(_a0,function(_){var _=wMV(E(_9y),new T1(1,_a2));return new F(function(){return A(_9t,[_9F,_9H,_a2,_]);});}));});return new F(function(){return A3(_4P,_9K,_a3,_9I);});};return B(A2(_9A,_9D,_a1));});return new F(function(){return A3(_4P,_9K,_9Z,_9R);});},_a4=new T(function(){return eval("(function(e,c,x){x?e.classList.add(c):e.classList.remove(c);})");}),_a5=function(_a6,_){var _a7=B(A1(_9p,_)),_a8=E(_a7);if(!_a8._){return new F(function(){return die(_7Y);});}else{var _a9=E(_a8.a),_aa=E(_7C),_ab=__app1(_aa,_a9),_ac=B(_8w(_a9,_a6,_)),_ad=B(A1(_7J,_)),_ae=E(_ad);if(!_ae._){return new F(function(){return die(_7V);});}else{var _af=_ae.a,_ag=B(A1(_7Q,_)),_ah=function(_){var _ai=__app1(E(_8r),toJSStr(E(_7S))),_aj=__app3(E(_7E),_ai,toJSStr(E(_7Z)),toJSStr(E(_7R))),_ak=E(_a4),_al=__app3(_ak,_ai,toJSStr(E(_7H)),true),_am=__app3(_ak,_ai,toJSStr(E(_7G)),true),_an=__app1(E(_9q),toJSStr(E(_7F))),_ao=E(_7B),_ap=__app2(_ao,_an,_ai),_aq=__app2(_ao,_ai,E(_af));return _ai;},_ar=E(_ag);if(!_ar._){var _as=B(_ah(_)),_at=function(_au,_){var _av=function(_aw,_){var _ax=B(A1(_9p,_)),_ay=E(_ax);if(!_ay._){return new F(function(){return die(_7Y);});}else{var _az=E(_ay.a),_aA=__app1(_aa,_az),_aB=B(_8w(_az,_aw,_)),_aC=B(A1(_7J,_)),_aD=E(_aC);if(!_aD._){return new F(function(){return die(_7V);});}else{var _aE=_aD.a,_aF=B(A1(_7Q,_)),_aG=function(_){var _aH=__app1(E(_8r),toJSStr(E(_7S))),_aI=__app3(E(_7E),_aH,toJSStr(E(_7Z)),toJSStr(E(_7R))),_aJ=E(_a4),_aK=__app3(_aJ,_aH,toJSStr(E(_7H)),true),_aL=__app3(_aJ,_aH,toJSStr(E(_7G)),true),_aM=__app1(E(_9q),toJSStr(E(_7F))),_aN=E(_7B),_aO=__app2(_aN,_aM,_aH),_aP=__app2(_aN,_aH,E(_aE));return _aH;},_aQ=E(_aF);if(!_aQ._){var _aR=B(_aG(_)),_aS=B(A(_9C,[_42,_3j,_3e,_aR,_44,function(_aT,_){return new F(function(){return _av(_aw,_);});},_]));return _43;}else{var _aU=__app2(E(_7D),E(_aQ.a),E(_aE)),_aV=B(_aG(_)),_aW=B(A(_9C,[_42,_3j,_3e,_aV,_44,function(_aX,_){return new F(function(){return _av(_aw,_);});},_]));return _43;}}}};return new F(function(){return _av(_a6,_);});},_aY=B(A(_9C,[_42,_3j,_3e,_as,_44,_at,_]));return _43;}else{var _aZ=E(_7D),_b0=__app2(_aZ,E(_ar.a),E(_af)),_b1=B(_ah(_)),_b2=function(_b3,_){var _b4=function(_b5,_){var _b6=B(A1(_9p,_)),_b7=E(_b6);if(!_b7._){return new F(function(){return die(_7Y);});}else{var _b8=E(_b7.a),_b9=__app1(_aa,_b8),_ba=B(_8w(_b8,_b5,_)),_bb=B(A1(_7J,_)),_bc=E(_bb);if(!_bc._){return new F(function(){return die(_7V);});}else{var _bd=_bc.a,_be=B(A1(_7Q,_)),_bf=function(_){var _bg=__app1(E(_8r),toJSStr(E(_7S))),_bh=__app3(E(_7E),_bg,toJSStr(E(_7Z)),toJSStr(E(_7R))),_bi=E(_a4),_bj=__app3(_bi,_bg,toJSStr(E(_7H)),true),_bk=__app3(_bi,_bg,toJSStr(E(_7G)),true),_bl=__app1(E(_9q),toJSStr(E(_7F))),_bm=E(_7B),_bn=__app2(_bm,_bl,_bg),_bo=__app2(_bm,_bg,E(_bd));return _bg;},_bp=E(_be);if(!_bp._){var _bq=B(_bf(_)),_br=B(A(_9C,[_42,_3j,_3e,_bq,_44,function(_bs,_){return new F(function(){return _b4(_b5,_);});},_]));return _43;}else{var _bt=__app2(_aZ,E(_bp.a),E(_bd)),_bu=B(_bf(_)),_bv=B(A(_9C,[_42,_3j,_3e,_bu,_44,function(_bw,_){return new F(function(){return _b4(_b5,_);});},_]));return _43;}}}};return new F(function(){return _b4(_a6,_);});},_bx=B(A(_9C,[_42,_3j,_3e,_b1,_44,_b2,_]));return _43;}}}},_by=46,_bz=function(_bA){var _bB=E(_bA);return (_bB==1)?new T2(0,_by,_v):new T2(0,_by,new T(function(){var _bC=B(_bz(_bB-1|0));return new T2(1,_bC.a,_bC.b);}));},_bD=new T(function(){var _bE=B(_bz(9));return new T2(1,_bE.a,_bE.b);}),_bF=function(_bG){var _bH=E(_bG);return (_bH==1)?new T2(0,_bD,_v):new T2(0,_bD,new T(function(){var _bI=B(_bF(_bH-1|0));return new T2(1,_bI.a,_bI.b);}));},_bJ=new T(function(){var _bK=B(_bF(9));return new T2(1,_bK.a,_bK.b);}),_bL=new T(function(){return B(unCStr("Blank"));}),_bM=new T2(0,_bL,_bJ),_bN=new T2(1,_bM,_v),_bO=new T(function(){return B(unCStr("Minimal"));}),_bP=new T(function(){return B(unCStr("....7...."));}),_bQ=new T(function(){return B(unCStr("....15..."));}),_bR=new T(function(){return B(unCStr("1........"));}),_bS=new T(function(){return B(unCStr("...2....9"));}),_bT=new T(function(){return B(unCStr("...9.6.82"));}),_bU=new T(function(){return B(unCStr(".......3."));}),_bV=new T(function(){return B(unCStr("5.1......"));}),_bW=new T(function(){return B(unCStr("...4...2."));}),_bX=new T2(1,_bW,_v),_bY=new T2(1,_bV,_bX),_bZ=new T2(1,_bU,_bY),_c0=new T2(1,_bT,_bZ),_c1=new T2(1,_bS,_c0),_c2=new T2(1,_bR,_c1),_c3=new T2(1,_bQ,_c2),_c4=new T2(1,_bP,_c3),_c5=new T(function(){return B(unCStr(".98......"));}),_c6=new T2(1,_c5,_c4),_c7=new T2(0,_bO,_c6),_c8=new T2(1,_c7,_bN),_c9=new T(function(){return B(unCStr("Unsolvable"));}),_ca=new T(function(){return B(unCStr(".8.....7."));}),_cb=new T(function(){return B(unCStr("..9...6.."));}),_cc=new T(function(){return B(unCStr("..72.94.."));}),_cd=new T(function(){return B(unCStr("41.....95"));}),_ce=new T(function(){return B(unCStr("..85.43.."));}),_cf=new T(function(){return B(unCStr("..3...7.."));}),_cg=new T(function(){return B(unCStr(".5.....4."));}),_ch=new T(function(){return B(unCStr("2..8.6..9"));}),_ci=new T2(1,_ch,_v),_cj=new T2(1,_cg,_ci),_ck=new T2(1,_cf,_cj),_cl=new T2(1,_ce,_ck),_cm=new T2(1,_cd,_cl),_cn=new T2(1,_cc,_cm),_co=new T2(1,_cb,_cn),_cp=new T2(1,_ca,_co),_cq=new T(function(){return B(unCStr("1..9.7..3"));}),_cr=new T2(1,_cq,_cp),_cs=new T2(0,_c9,_cr),_ct=new T2(1,_cs,_c8),_cu=new T(function(){return B(unCStr(".31..5.2."));}),_cv=new T(function(){return B(unCStr("8.6......"));}),_cw=new T(function(){return B(unCStr("..7.5...6"));}),_cx=new T(function(){return B(unCStr("...3.7..."));}),_cy=new T(function(){return B(unCStr("5...1.7.."));}),_cz=new T(function(){return B(unCStr("......1.9"));}),_cA=new T(function(){return B(unCStr(".2.6..35."));}),_cB=new T(function(){return B(unCStr(".54..8.7."));}),_cC=new T2(1,_cB,_v),_cD=new T2(1,_cA,_cC),_cE=new T2(1,_cz,_cD),_cF=new T2(1,_cy,_cE),_cG=new T2(1,_cx,_cF),_cH=new T2(1,_cw,_cG),_cI=new T2(1,_cv,_cH),_cJ=new T2(1,_cu,_cI),_cK=new T(function(){return B(unCStr(".9.7..86."));}),_cL=new T2(1,_cK,_cJ),_cM=new T(function(){return B(unCStr("Diabolical"));}),_cN=new T2(0,_cM,_cL),_cO=new T2(1,_cN,_ct),_cP=new T(function(){return B(unCStr("..2.71.39"));}),_cQ=new T(function(){return B(unCStr(".......4."));}),_cR=new T(function(){return B(unCStr("2.71....6"));}),_cS=new T(function(){return B(unCStr("....4...."));}),_cT=new T(function(){return B(unCStr("6....74.3"));}),_cU=new T(function(){return B(unCStr(".7......."));}),_cV=new T(function(){return B(unCStr("12.73.5.."));}),_cW=new T(function(){return B(unCStr("3...82.7."));}),_cX=new T2(1,_cW,_v),_cY=new T2(1,_cV,_cX),_cZ=new T2(1,_cU,_cY),_d0=new T2(1,_cT,_cZ),_d1=new T2(1,_cS,_d0),_d2=new T2(1,_cR,_d1),_d3=new T2(1,_cQ,_d2),_d4=new T2(1,_cP,_d3),_d5=new T(function(){return B(unCStr(".1.42...5"));}),_d6=new T2(1,_d5,_d4),_d7=new T(function(){return B(unCStr("Gentle"));}),_d8=new T2(0,_d7,_d6),_d9=new T2(1,_d8,_cO),_da=new T(function(){return B(unCStr("........5"));}),_db=new T(function(){return B(unCStr(".7...6..."));}),_dc=new T(function(){return B(unCStr(".......13"));}),_dd=new T(function(){return B(unCStr(".981..257"));}),_de=new T(function(){return B(unCStr("31....8.."));}),_df=new T(function(){return B(unCStr("9..8...2."));}),_dg=new T(function(){return B(unCStr(".5..69784"));}),_dh=new T(function(){return B(unCStr("4..25...."));}),_di=new T2(1,_dh,_v),_dj=new T2(1,_dg,_di),_dk=new T2(1,_df,_dj),_dl=new T2(1,_de,_dk),_dm=new T2(1,_dd,_dl),_dn=new T2(1,_dc,_dm),_do=new T2(1,_db,_dn),_dp=new T2(1,_da,_do),_dq=new T(function(){return B(unCStr("2....1.38"));}),_dr=new T2(1,_dq,_dp),_ds=new T(function(){return B(unCStr("Easy"));}),_dt=new T2(0,_ds,_dr),_du=new T2(1,_dt,_d9),_dv=new T(function(){return B(_7y(_du,0));}),_dw=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_dx=new T(function(){return B(err(_dw));}),_dy=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_dz=new T(function(){return B(err(_dy));}),_dA=new T(function(){return B(unCStr("base"));}),_dB=new T(function(){return B(unCStr("Control.Exception.Base"));}),_dC=new T(function(){return B(unCStr("PatternMatchFail"));}),_dD=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dA,_dB,_dC),_dE=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_dD,_v,_v),_dF=function(_dG){return E(_dE);},_dH=function(_dI){var _dJ=E(_dI);return new F(function(){return _X(B(_V(_dJ.a)),_dF,_dJ.b);});},_dK=function(_dL){return E(E(_dL).a);},_dM=function(_dN){return new T2(0,_dO,_dN);},_dP=function(_dQ,_dR){return new F(function(){return _3(E(_dQ).a,_dR);});},_dS=function(_dT,_dU){return new F(function(){return _28(_dP,_dT,_dU);});},_dV=function(_dW,_dX,_dY){return new F(function(){return _3(E(_dX).a,_dY);});},_dZ=new T3(0,_dV,_dK,_dS),_dO=new T(function(){return new T5(0,_dF,_dZ,_dM,_dH,_dK);}),_e0=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_e1=function(_e2,_e3){return new F(function(){return die(new T(function(){return B(A2(_3L,_e3,_e2));}));});},_e4=function(_e5,_e6){return new F(function(){return _e1(_e5,_e6);});},_e7=function(_e8,_e9){var _ea=E(_e9);if(!_ea._){return new T2(0,_v,_v);}else{var _eb=_ea.a;if(!B(A1(_e8,_eb))){return new T2(0,_v,_ea);}else{var _ec=new T(function(){var _ed=B(_e7(_e8,_ea.b));return new T2(0,_ed.a,_ed.b);});return new T2(0,new T2(1,_eb,new T(function(){return E(E(_ec).a);})),new T(function(){return E(E(_ec).b);}));}}},_ee=32,_ef=new T(function(){return B(unCStr("\n"));}),_eg=function(_eh){return (E(_eh)==124)?false:true;},_ei=function(_ej,_ek){var _el=B(_e7(_eg,B(unCStr(_ej)))),_em=_el.a,_en=function(_eo,_ep){var _eq=new T(function(){var _er=new T(function(){return B(_3(_ek,new T(function(){return B(_3(_ep,_ef));},1)));});return B(unAppCStr(": ",_er));},1);return new F(function(){return _3(_eo,_eq);});},_es=E(_el.b);if(!_es._){return new F(function(){return _en(_em,_v);});}else{if(E(_es.a)==124){return new F(function(){return _en(_em,new T2(1,_ee,_es.b));});}else{return new F(function(){return _en(_em,_v);});}}},_et=function(_eu){return new F(function(){return _e4(new T1(0,new T(function(){return B(_ei(_eu,_e0));})),_dO);});},_ev=new T(function(){return B(_et("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_ew=function(_ex,_ey){while(1){var _ez=B((function(_eA,_eB){var _eC=E(_eA);switch(_eC._){case 0:var _eD=E(_eB);if(!_eD._){return __Z;}else{_ex=B(A1(_eC.a,_eD.a));_ey=_eD.b;return __continue;}break;case 1:var _eE=B(A1(_eC.a,_eB)),_eF=_eB;_ex=_eE;_ey=_eF;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_eC.a,_eB),new T(function(){return B(_ew(_eC.b,_eB));}));default:return E(_eC.a);}})(_ex,_ey));if(_ez!=__continue){return _ez;}}},_eG=function(_eH,_eI){var _eJ=function(_eK){var _eL=E(_eI);if(_eL._==3){return new T2(3,_eL.a,new T(function(){return B(_eG(_eH,_eL.b));}));}else{var _eM=E(_eH);if(_eM._==2){return E(_eL);}else{var _eN=E(_eL);if(_eN._==2){return E(_eM);}else{var _eO=function(_eP){var _eQ=E(_eN);if(_eQ._==4){var _eR=function(_eS){return new T1(4,new T(function(){return B(_3(B(_ew(_eM,_eS)),_eQ.a));}));};return new T1(1,_eR);}else{var _eT=E(_eM);if(_eT._==1){var _eU=_eT.a,_eV=E(_eQ);if(!_eV._){return new T1(1,function(_eW){return new F(function(){return _eG(B(A1(_eU,_eW)),_eV);});});}else{var _eX=function(_eY){return new F(function(){return _eG(B(A1(_eU,_eY)),new T(function(){return B(A1(_eV.a,_eY));}));});};return new T1(1,_eX);}}else{var _eZ=E(_eQ);if(!_eZ._){return E(_ev);}else{var _f0=function(_f1){return new F(function(){return _eG(_eT,new T(function(){return B(A1(_eZ.a,_f1));}));});};return new T1(1,_f0);}}}},_f2=E(_eM);switch(_f2._){case 1:var _f3=E(_eN);if(_f3._==4){var _f4=function(_f5){return new T1(4,new T(function(){return B(_3(B(_ew(B(A1(_f2.a,_f5)),_f5)),_f3.a));}));};return new T1(1,_f4);}else{return new F(function(){return _eO(_);});}break;case 4:var _f6=_f2.a,_f7=E(_eN);switch(_f7._){case 0:var _f8=function(_f9){var _fa=new T(function(){return B(_3(_f6,new T(function(){return B(_ew(_f7,_f9));},1)));});return new T1(4,_fa);};return new T1(1,_f8);case 1:var _fb=function(_fc){var _fd=new T(function(){return B(_3(_f6,new T(function(){return B(_ew(B(A1(_f7.a,_fc)),_fc));},1)));});return new T1(4,_fd);};return new T1(1,_fb);default:return new T1(4,new T(function(){return B(_3(_f6,_f7.a));}));}break;default:return new F(function(){return _eO(_);});}}}}},_fe=E(_eH);switch(_fe._){case 0:var _ff=E(_eI);if(!_ff._){var _fg=function(_fh){return new F(function(){return _eG(B(A1(_fe.a,_fh)),new T(function(){return B(A1(_ff.a,_fh));}));});};return new T1(0,_fg);}else{return new F(function(){return _eJ(_);});}break;case 3:return new T2(3,_fe.a,new T(function(){return B(_eG(_fe.b,_eI));}));default:return new F(function(){return _eJ(_);});}},_fi=new T(function(){return B(unCStr("("));}),_fj=new T(function(){return B(unCStr(")"));}),_fk=function(_fl,_fm){while(1){var _fn=E(_fl);if(!_fn._){return (E(_fm)._==0)?true:false;}else{var _fo=E(_fm);if(!_fo._){return false;}else{if(E(_fn.a)!=E(_fo.a)){return false;}else{_fl=_fn.b;_fm=_fo.b;continue;}}}}},_fp=function(_fq,_fr){while(1){var _fs=E(_fq);if(!_fs._){return (E(_fr)._==0)?true:false;}else{var _ft=E(_fr);if(!_ft._){return false;}else{if(E(_fs.a)!=E(_ft.a)){return false;}else{_fq=_fs.b;_fr=_ft.b;continue;}}}}},_fu=function(_fv,_fw){return (!B(_fp(_fv,_fw)))?true:false;},_fx=new T2(0,_fp,_fu),_fy=function(_fz,_fA){var _fB=E(_fz);switch(_fB._){case 0:return new T1(0,function(_fC){return new F(function(){return _fy(B(A1(_fB.a,_fC)),_fA);});});case 1:return new T1(1,function(_fD){return new F(function(){return _fy(B(A1(_fB.a,_fD)),_fA);});});case 2:return new T0(2);case 3:return new F(function(){return _eG(B(A1(_fA,_fB.a)),new T(function(){return B(_fy(_fB.b,_fA));}));});break;default:var _fE=function(_fF){var _fG=E(_fF);if(!_fG._){return __Z;}else{var _fH=E(_fG.a);return new F(function(){return _3(B(_ew(B(A1(_fA,_fH.a)),_fH.b)),new T(function(){return B(_fE(_fG.b));},1));});}},_fI=B(_fE(_fB.a));return (_fI._==0)?new T0(2):new T1(4,_fI);}},_fJ=new T0(2),_fK=function(_fL){return new T2(3,_fL,_fJ);},_fM=function(_fN,_fO){var _fP=E(_fN);if(!_fP){return new F(function(){return A1(_fO,_43);});}else{var _fQ=new T(function(){return B(_fM(_fP-1|0,_fO));});return new T1(0,function(_fR){return E(_fQ);});}},_fS=function(_fT,_fU,_fV){var _fW=new T(function(){return B(A1(_fT,_fK));}),_fX=function(_fY,_fZ,_g0,_g1){while(1){var _g2=B((function(_g3,_g4,_g5,_g6){var _g7=E(_g3);switch(_g7._){case 0:var _g8=E(_g4);if(!_g8._){return new F(function(){return A1(_fU,_g6);});}else{var _g9=_g5+1|0,_ga=_g6;_fY=B(A1(_g7.a,_g8.a));_fZ=_g8.b;_g0=_g9;_g1=_ga;return __continue;}break;case 1:var _gb=B(A1(_g7.a,_g4)),_gc=_g4,_g9=_g5,_ga=_g6;_fY=_gb;_fZ=_gc;_g0=_g9;_g1=_ga;return __continue;case 2:return new F(function(){return A1(_fU,_g6);});break;case 3:var _gd=new T(function(){return B(_fy(_g7,_g6));});return new F(function(){return _fM(_g5,function(_ge){return E(_gd);});});break;default:return new F(function(){return _fy(_g7,_g6);});}})(_fY,_fZ,_g0,_g1));if(_g2!=__continue){return _g2;}}};return function(_gf){return new F(function(){return _fX(_fW,_gf,0,_fV);});};},_gg=function(_gh){return new F(function(){return A1(_gh,_v);});},_gi=function(_gj,_gk){var _gl=function(_gm){var _gn=E(_gm);if(!_gn._){return E(_gg);}else{var _go=_gn.a;if(!B(A1(_gj,_go))){return E(_gg);}else{var _gp=new T(function(){return B(_gl(_gn.b));}),_gq=function(_gr){var _gs=new T(function(){return B(A1(_gp,function(_gt){return new F(function(){return A1(_gr,new T2(1,_go,_gt));});}));});return new T1(0,function(_gu){return E(_gs);});};return E(_gq);}}};return function(_gv){return new F(function(){return A2(_gl,_gv,_gk);});};},_gw=new T0(6),_gx=new T(function(){return B(unCStr("valDig: Bad base"));}),_gy=new T(function(){return B(err(_gx));}),_gz=function(_gA,_gB){var _gC=function(_gD,_gE){var _gF=E(_gD);if(!_gF._){var _gG=new T(function(){return B(A1(_gE,_v));});return function(_gH){return new F(function(){return A1(_gH,_gG);});};}else{var _gI=E(_gF.a),_gJ=function(_gK){var _gL=new T(function(){return B(_gC(_gF.b,function(_gM){return new F(function(){return A1(_gE,new T2(1,_gK,_gM));});}));}),_gN=function(_gO){var _gP=new T(function(){return B(A1(_gL,_gO));});return new T1(0,function(_gQ){return E(_gP);});};return E(_gN);};switch(E(_gA)){case 8:if(48>_gI){var _gR=new T(function(){return B(A1(_gE,_v));});return function(_gS){return new F(function(){return A1(_gS,_gR);});};}else{if(_gI>55){var _gT=new T(function(){return B(A1(_gE,_v));});return function(_gU){return new F(function(){return A1(_gU,_gT);});};}else{return new F(function(){return _gJ(_gI-48|0);});}}break;case 10:if(48>_gI){var _gV=new T(function(){return B(A1(_gE,_v));});return function(_gW){return new F(function(){return A1(_gW,_gV);});};}else{if(_gI>57){var _gX=new T(function(){return B(A1(_gE,_v));});return function(_gY){return new F(function(){return A1(_gY,_gX);});};}else{return new F(function(){return _gJ(_gI-48|0);});}}break;case 16:if(48>_gI){if(97>_gI){if(65>_gI){var _gZ=new T(function(){return B(A1(_gE,_v));});return function(_h0){return new F(function(){return A1(_h0,_gZ);});};}else{if(_gI>70){var _h1=new T(function(){return B(A1(_gE,_v));});return function(_h2){return new F(function(){return A1(_h2,_h1);});};}else{return new F(function(){return _gJ((_gI-65|0)+10|0);});}}}else{if(_gI>102){if(65>_gI){var _h3=new T(function(){return B(A1(_gE,_v));});return function(_h4){return new F(function(){return A1(_h4,_h3);});};}else{if(_gI>70){var _h5=new T(function(){return B(A1(_gE,_v));});return function(_h6){return new F(function(){return A1(_h6,_h5);});};}else{return new F(function(){return _gJ((_gI-65|0)+10|0);});}}}else{return new F(function(){return _gJ((_gI-97|0)+10|0);});}}}else{if(_gI>57){if(97>_gI){if(65>_gI){var _h7=new T(function(){return B(A1(_gE,_v));});return function(_h8){return new F(function(){return A1(_h8,_h7);});};}else{if(_gI>70){var _h9=new T(function(){return B(A1(_gE,_v));});return function(_ha){return new F(function(){return A1(_ha,_h9);});};}else{return new F(function(){return _gJ((_gI-65|0)+10|0);});}}}else{if(_gI>102){if(65>_gI){var _hb=new T(function(){return B(A1(_gE,_v));});return function(_hc){return new F(function(){return A1(_hc,_hb);});};}else{if(_gI>70){var _hd=new T(function(){return B(A1(_gE,_v));});return function(_he){return new F(function(){return A1(_he,_hd);});};}else{return new F(function(){return _gJ((_gI-65|0)+10|0);});}}}else{return new F(function(){return _gJ((_gI-97|0)+10|0);});}}}else{return new F(function(){return _gJ(_gI-48|0);});}}break;default:return E(_gy);}}},_hf=function(_hg){var _hh=E(_hg);if(!_hh._){return new T0(2);}else{return new F(function(){return A1(_gB,_hh);});}};return function(_hi){return new F(function(){return A3(_gC,_hi,_3h,_hf);});};},_hj=16,_hk=8,_hl=function(_hm){var _hn=function(_ho){return new F(function(){return A1(_hm,new T1(5,new T2(0,_hk,_ho)));});},_hp=function(_hq){return new F(function(){return A1(_hm,new T1(5,new T2(0,_hj,_hq)));});},_hr=function(_hs){switch(E(_hs)){case 79:return new T1(1,B(_gz(_hk,_hn)));case 88:return new T1(1,B(_gz(_hj,_hp)));case 111:return new T1(1,B(_gz(_hk,_hn)));case 120:return new T1(1,B(_gz(_hj,_hp)));default:return new T0(2);}};return function(_ht){return (E(_ht)==48)?E(new T1(0,_hr)):new T0(2);};},_hu=function(_hv){return new T1(0,B(_hl(_hv)));},_hw=function(_hx){return new F(function(){return A1(_hx,_2q);});},_hy=function(_hz){return new F(function(){return A1(_hz,_2q);});},_hA=10,_hB=new T1(0,1),_hC=new T1(0,2147483647),_hD=function(_hE,_hF){while(1){var _hG=E(_hE);if(!_hG._){var _hH=_hG.a,_hI=E(_hF);if(!_hI._){var _hJ=_hI.a,_hK=addC(_hH,_hJ);if(!E(_hK.b)){return new T1(0,_hK.a);}else{_hE=new T1(1,I_fromInt(_hH));_hF=new T1(1,I_fromInt(_hJ));continue;}}else{_hE=new T1(1,I_fromInt(_hH));_hF=_hI;continue;}}else{var _hL=E(_hF);if(!_hL._){_hE=_hG;_hF=new T1(1,I_fromInt(_hL.a));continue;}else{return new T1(1,I_add(_hG.a,_hL.a));}}}},_hM=new T(function(){return B(_hD(_hC,_hB));}),_hN=function(_hO){var _hP=E(_hO);if(!_hP._){var _hQ=E(_hP.a);return (_hQ==(-2147483648))?E(_hM):new T1(0, -_hQ);}else{return new T1(1,I_negate(_hP.a));}},_hR=new T1(0,10),_hS=function(_hT,_hU){while(1){var _hV=E(_hT);if(!_hV._){return E(_hU);}else{var _hW=_hU+1|0;_hT=_hV.b;_hU=_hW;continue;}}},_hX=function(_hY){return new T1(0,_hY);},_hZ=function(_i0){return new F(function(){return _hX(E(_i0));});},_i1=new T(function(){return B(unCStr("this should not happen"));}),_i2=new T(function(){return B(err(_i1));}),_i3=function(_i4,_i5){while(1){var _i6=E(_i4);if(!_i6._){var _i7=_i6.a,_i8=E(_i5);if(!_i8._){var _i9=_i8.a;if(!(imul(_i7,_i9)|0)){return new T1(0,imul(_i7,_i9)|0);}else{_i4=new T1(1,I_fromInt(_i7));_i5=new T1(1,I_fromInt(_i9));continue;}}else{_i4=new T1(1,I_fromInt(_i7));_i5=_i8;continue;}}else{var _ia=E(_i5);if(!_ia._){_i4=_i6;_i5=new T1(1,I_fromInt(_ia.a));continue;}else{return new T1(1,I_mul(_i6.a,_ia.a));}}}},_ib=function(_ic,_id){var _ie=E(_id);if(!_ie._){return __Z;}else{var _if=E(_ie.b);return (_if._==0)?E(_i2):new T2(1,B(_hD(B(_i3(_ie.a,_ic)),_if.a)),new T(function(){return B(_ib(_ic,_if.b));}));}},_ig=new T1(0,0),_ih=function(_ii,_ij,_ik){while(1){var _il=B((function(_im,_in,_io){var _ip=E(_io);if(!_ip._){return E(_ig);}else{if(!E(_ip.b)._){return E(_ip.a);}else{var _iq=E(_in);if(_iq<=40){var _ir=function(_is,_it){while(1){var _iu=E(_it);if(!_iu._){return E(_is);}else{var _iv=B(_hD(B(_i3(_is,_im)),_iu.a));_is=_iv;_it=_iu.b;continue;}}};return new F(function(){return _ir(_ig,_ip);});}else{var _iw=B(_i3(_im,_im));if(!(_iq%2)){var _ix=B(_ib(_im,_ip));_ii=_iw;_ij=quot(_iq+1|0,2);_ik=_ix;return __continue;}else{var _ix=B(_ib(_im,new T2(1,_ig,_ip)));_ii=_iw;_ij=quot(_iq+1|0,2);_ik=_ix;return __continue;}}}}})(_ii,_ij,_ik));if(_il!=__continue){return _il;}}},_iy=function(_iz,_iA){return new F(function(){return _ih(_iz,new T(function(){return B(_hS(_iA,0));},1),B(_60(_hZ,_iA)));});},_iB=function(_iC){var _iD=new T(function(){var _iE=new T(function(){var _iF=function(_iG){return new F(function(){return A1(_iC,new T1(1,new T(function(){return B(_iy(_hR,_iG));})));});};return new T1(1,B(_gz(_hA,_iF)));}),_iH=function(_iI){if(E(_iI)==43){var _iJ=function(_iK){return new F(function(){return A1(_iC,new T1(1,new T(function(){return B(_iy(_hR,_iK));})));});};return new T1(1,B(_gz(_hA,_iJ)));}else{return new T0(2);}},_iL=function(_iM){if(E(_iM)==45){var _iN=function(_iO){return new F(function(){return A1(_iC,new T1(1,new T(function(){return B(_hN(B(_iy(_hR,_iO))));})));});};return new T1(1,B(_gz(_hA,_iN)));}else{return new T0(2);}};return B(_eG(B(_eG(new T1(0,_iL),new T1(0,_iH))),_iE));});return new F(function(){return _eG(new T1(0,function(_iP){return (E(_iP)==101)?E(_iD):new T0(2);}),new T1(0,function(_iQ){return (E(_iQ)==69)?E(_iD):new T0(2);}));});},_iR=function(_iS){var _iT=function(_iU){return new F(function(){return A1(_iS,new T1(1,_iU));});};return function(_iV){return (E(_iV)==46)?new T1(1,B(_gz(_hA,_iT))):new T0(2);};},_iW=function(_iX){return new T1(0,B(_iR(_iX)));},_iY=function(_iZ){var _j0=function(_j1){var _j2=function(_j3){return new T1(1,B(_fS(_iB,_hw,function(_j4){return new F(function(){return A1(_iZ,new T1(5,new T3(1,_j1,_j3,_j4)));});})));};return new T1(1,B(_fS(_iW,_hy,_j2)));};return new F(function(){return _gz(_hA,_j0);});},_j5=function(_j6){return new T1(1,B(_iY(_j6)));},_j7=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_j8=function(_j9){return new F(function(){return _6N(_6K,_j9,_j7);});},_ja=false,_jb=true,_jc=function(_jd){var _je=new T(function(){return B(A1(_jd,_hk));}),_jf=new T(function(){return B(A1(_jd,_hj));});return function(_jg){switch(E(_jg)){case 79:return E(_je);case 88:return E(_jf);case 111:return E(_je);case 120:return E(_jf);default:return new T0(2);}};},_jh=function(_ji){return new T1(0,B(_jc(_ji)));},_jj=function(_jk){return new F(function(){return A1(_jk,_hA);});},_jl=function(_jm){var _jn=E(_jm);if(!_jn._){return E(_jn.a);}else{return new F(function(){return I_toInt(_jn.a);});}},_jo=function(_jp,_jq){var _jr=E(_jp);if(!_jr._){var _js=_jr.a,_jt=E(_jq);return (_jt._==0)?_js<=_jt.a:I_compareInt(_jt.a,_js)>=0;}else{var _ju=_jr.a,_jv=E(_jq);return (_jv._==0)?I_compareInt(_ju,_jv.a)<=0:I_compare(_ju,_jv.a)<=0;}},_jw=function(_jx){return new T0(2);},_jy=function(_jz){var _jA=E(_jz);if(!_jA._){return E(_jw);}else{var _jB=_jA.a,_jC=E(_jA.b);if(!_jC._){return E(_jB);}else{var _jD=new T(function(){return B(_jy(_jC));}),_jE=function(_jF){return new F(function(){return _eG(B(A1(_jB,_jF)),new T(function(){return B(A1(_jD,_jF));}));});};return E(_jE);}}},_jG=function(_jH,_jI){var _jJ=function(_jK,_jL,_jM){var _jN=E(_jK);if(!_jN._){return new F(function(){return A1(_jM,_jH);});}else{var _jO=E(_jL);if(!_jO._){return new T0(2);}else{if(E(_jN.a)!=E(_jO.a)){return new T0(2);}else{var _jP=new T(function(){return B(_jJ(_jN.b,_jO.b,_jM));});return new T1(0,function(_jQ){return E(_jP);});}}}};return function(_jR){return new F(function(){return _jJ(_jH,_jR,_jI);});};},_jS=new T(function(){return B(unCStr("SO"));}),_jT=14,_jU=function(_jV){var _jW=new T(function(){return B(A1(_jV,_jT));});return new T1(1,B(_jG(_jS,function(_jX){return E(_jW);})));},_jY=new T(function(){return B(unCStr("SOH"));}),_jZ=1,_k0=function(_k1){var _k2=new T(function(){return B(A1(_k1,_jZ));});return new T1(1,B(_jG(_jY,function(_k3){return E(_k2);})));},_k4=function(_k5){return new T1(1,B(_fS(_k0,_jU,_k5)));},_k6=new T(function(){return B(unCStr("NUL"));}),_k7=0,_k8=function(_k9){var _ka=new T(function(){return B(A1(_k9,_k7));});return new T1(1,B(_jG(_k6,function(_kb){return E(_ka);})));},_kc=new T(function(){return B(unCStr("STX"));}),_kd=2,_ke=function(_kf){var _kg=new T(function(){return B(A1(_kf,_kd));});return new T1(1,B(_jG(_kc,function(_kh){return E(_kg);})));},_ki=new T(function(){return B(unCStr("ETX"));}),_kj=3,_kk=function(_kl){var _km=new T(function(){return B(A1(_kl,_kj));});return new T1(1,B(_jG(_ki,function(_kn){return E(_km);})));},_ko=new T(function(){return B(unCStr("EOT"));}),_kp=4,_kq=function(_kr){var _ks=new T(function(){return B(A1(_kr,_kp));});return new T1(1,B(_jG(_ko,function(_kt){return E(_ks);})));},_ku=new T(function(){return B(unCStr("ENQ"));}),_kv=5,_kw=function(_kx){var _ky=new T(function(){return B(A1(_kx,_kv));});return new T1(1,B(_jG(_ku,function(_kz){return E(_ky);})));},_kA=new T(function(){return B(unCStr("ACK"));}),_kB=6,_kC=function(_kD){var _kE=new T(function(){return B(A1(_kD,_kB));});return new T1(1,B(_jG(_kA,function(_kF){return E(_kE);})));},_kG=new T(function(){return B(unCStr("BEL"));}),_kH=7,_kI=function(_kJ){var _kK=new T(function(){return B(A1(_kJ,_kH));});return new T1(1,B(_jG(_kG,function(_kL){return E(_kK);})));},_kM=new T(function(){return B(unCStr("BS"));}),_kN=8,_kO=function(_kP){var _kQ=new T(function(){return B(A1(_kP,_kN));});return new T1(1,B(_jG(_kM,function(_kR){return E(_kQ);})));},_kS=new T(function(){return B(unCStr("HT"));}),_kT=9,_kU=function(_kV){var _kW=new T(function(){return B(A1(_kV,_kT));});return new T1(1,B(_jG(_kS,function(_kX){return E(_kW);})));},_kY=new T(function(){return B(unCStr("LF"));}),_kZ=10,_l0=function(_l1){var _l2=new T(function(){return B(A1(_l1,_kZ));});return new T1(1,B(_jG(_kY,function(_l3){return E(_l2);})));},_l4=new T(function(){return B(unCStr("VT"));}),_l5=11,_l6=function(_l7){var _l8=new T(function(){return B(A1(_l7,_l5));});return new T1(1,B(_jG(_l4,function(_l9){return E(_l8);})));},_la=new T(function(){return B(unCStr("FF"));}),_lb=12,_lc=function(_ld){var _le=new T(function(){return B(A1(_ld,_lb));});return new T1(1,B(_jG(_la,function(_lf){return E(_le);})));},_lg=new T(function(){return B(unCStr("CR"));}),_lh=13,_li=function(_lj){var _lk=new T(function(){return B(A1(_lj,_lh));});return new T1(1,B(_jG(_lg,function(_ll){return E(_lk);})));},_lm=new T(function(){return B(unCStr("SI"));}),_ln=15,_lo=function(_lp){var _lq=new T(function(){return B(A1(_lp,_ln));});return new T1(1,B(_jG(_lm,function(_lr){return E(_lq);})));},_ls=new T(function(){return B(unCStr("DLE"));}),_lt=16,_lu=function(_lv){var _lw=new T(function(){return B(A1(_lv,_lt));});return new T1(1,B(_jG(_ls,function(_lx){return E(_lw);})));},_ly=new T(function(){return B(unCStr("DC1"));}),_lz=17,_lA=function(_lB){var _lC=new T(function(){return B(A1(_lB,_lz));});return new T1(1,B(_jG(_ly,function(_lD){return E(_lC);})));},_lE=new T(function(){return B(unCStr("DC2"));}),_lF=18,_lG=function(_lH){var _lI=new T(function(){return B(A1(_lH,_lF));});return new T1(1,B(_jG(_lE,function(_lJ){return E(_lI);})));},_lK=new T(function(){return B(unCStr("DC3"));}),_lL=19,_lM=function(_lN){var _lO=new T(function(){return B(A1(_lN,_lL));});return new T1(1,B(_jG(_lK,function(_lP){return E(_lO);})));},_lQ=new T(function(){return B(unCStr("DC4"));}),_lR=20,_lS=function(_lT){var _lU=new T(function(){return B(A1(_lT,_lR));});return new T1(1,B(_jG(_lQ,function(_lV){return E(_lU);})));},_lW=new T(function(){return B(unCStr("NAK"));}),_lX=21,_lY=function(_lZ){var _m0=new T(function(){return B(A1(_lZ,_lX));});return new T1(1,B(_jG(_lW,function(_m1){return E(_m0);})));},_m2=new T(function(){return B(unCStr("SYN"));}),_m3=22,_m4=function(_m5){var _m6=new T(function(){return B(A1(_m5,_m3));});return new T1(1,B(_jG(_m2,function(_m7){return E(_m6);})));},_m8=new T(function(){return B(unCStr("ETB"));}),_m9=23,_ma=function(_mb){var _mc=new T(function(){return B(A1(_mb,_m9));});return new T1(1,B(_jG(_m8,function(_md){return E(_mc);})));},_me=new T(function(){return B(unCStr("CAN"));}),_mf=24,_mg=function(_mh){var _mi=new T(function(){return B(A1(_mh,_mf));});return new T1(1,B(_jG(_me,function(_mj){return E(_mi);})));},_mk=new T(function(){return B(unCStr("EM"));}),_ml=25,_mm=function(_mn){var _mo=new T(function(){return B(A1(_mn,_ml));});return new T1(1,B(_jG(_mk,function(_mp){return E(_mo);})));},_mq=new T(function(){return B(unCStr("SUB"));}),_mr=26,_ms=function(_mt){var _mu=new T(function(){return B(A1(_mt,_mr));});return new T1(1,B(_jG(_mq,function(_mv){return E(_mu);})));},_mw=new T(function(){return B(unCStr("ESC"));}),_mx=27,_my=function(_mz){var _mA=new T(function(){return B(A1(_mz,_mx));});return new T1(1,B(_jG(_mw,function(_mB){return E(_mA);})));},_mC=new T(function(){return B(unCStr("FS"));}),_mD=28,_mE=function(_mF){var _mG=new T(function(){return B(A1(_mF,_mD));});return new T1(1,B(_jG(_mC,function(_mH){return E(_mG);})));},_mI=new T(function(){return B(unCStr("GS"));}),_mJ=29,_mK=function(_mL){var _mM=new T(function(){return B(A1(_mL,_mJ));});return new T1(1,B(_jG(_mI,function(_mN){return E(_mM);})));},_mO=new T(function(){return B(unCStr("RS"));}),_mP=30,_mQ=function(_mR){var _mS=new T(function(){return B(A1(_mR,_mP));});return new T1(1,B(_jG(_mO,function(_mT){return E(_mS);})));},_mU=new T(function(){return B(unCStr("US"));}),_mV=31,_mW=function(_mX){var _mY=new T(function(){return B(A1(_mX,_mV));});return new T1(1,B(_jG(_mU,function(_mZ){return E(_mY);})));},_n0=new T(function(){return B(unCStr("SP"));}),_n1=32,_n2=function(_n3){var _n4=new T(function(){return B(A1(_n3,_n1));});return new T1(1,B(_jG(_n0,function(_n5){return E(_n4);})));},_n6=new T(function(){return B(unCStr("DEL"));}),_n7=127,_n8=function(_n9){var _na=new T(function(){return B(A1(_n9,_n7));});return new T1(1,B(_jG(_n6,function(_nb){return E(_na);})));},_nc=new T2(1,_n8,_v),_nd=new T2(1,_n2,_nc),_ne=new T2(1,_mW,_nd),_nf=new T2(1,_mQ,_ne),_ng=new T2(1,_mK,_nf),_nh=new T2(1,_mE,_ng),_ni=new T2(1,_my,_nh),_nj=new T2(1,_ms,_ni),_nk=new T2(1,_mm,_nj),_nl=new T2(1,_mg,_nk),_nm=new T2(1,_ma,_nl),_nn=new T2(1,_m4,_nm),_no=new T2(1,_lY,_nn),_np=new T2(1,_lS,_no),_nq=new T2(1,_lM,_np),_nr=new T2(1,_lG,_nq),_ns=new T2(1,_lA,_nr),_nt=new T2(1,_lu,_ns),_nu=new T2(1,_lo,_nt),_nv=new T2(1,_li,_nu),_nw=new T2(1,_lc,_nv),_nx=new T2(1,_l6,_nw),_ny=new T2(1,_l0,_nx),_nz=new T2(1,_kU,_ny),_nA=new T2(1,_kO,_nz),_nB=new T2(1,_kI,_nA),_nC=new T2(1,_kC,_nB),_nD=new T2(1,_kw,_nC),_nE=new T2(1,_kq,_nD),_nF=new T2(1,_kk,_nE),_nG=new T2(1,_ke,_nF),_nH=new T2(1,_k8,_nG),_nI=new T2(1,_k4,_nH),_nJ=new T(function(){return B(_jy(_nI));}),_nK=34,_nL=new T1(0,1114111),_nM=92,_nN=39,_nO=function(_nP){var _nQ=new T(function(){return B(A1(_nP,_kH));}),_nR=new T(function(){return B(A1(_nP,_kN));}),_nS=new T(function(){return B(A1(_nP,_kT));}),_nT=new T(function(){return B(A1(_nP,_kZ));}),_nU=new T(function(){return B(A1(_nP,_l5));}),_nV=new T(function(){return B(A1(_nP,_lb));}),_nW=new T(function(){return B(A1(_nP,_lh));}),_nX=new T(function(){return B(A1(_nP,_nM));}),_nY=new T(function(){return B(A1(_nP,_nN));}),_nZ=new T(function(){return B(A1(_nP,_nK));}),_o0=new T(function(){var _o1=function(_o2){var _o3=new T(function(){return B(_hX(E(_o2)));}),_o4=function(_o5){var _o6=B(_iy(_o3,_o5));if(!B(_jo(_o6,_nL))){return new T0(2);}else{return new F(function(){return A1(_nP,new T(function(){var _o7=B(_jl(_o6));if(_o7>>>0>1114111){return B(_7K(_o7));}else{return _o7;}}));});}};return new T1(1,B(_gz(_o2,_o4)));},_o8=new T(function(){var _o9=new T(function(){return B(A1(_nP,_mV));}),_oa=new T(function(){return B(A1(_nP,_mP));}),_ob=new T(function(){return B(A1(_nP,_mJ));}),_oc=new T(function(){return B(A1(_nP,_mD));}),_od=new T(function(){return B(A1(_nP,_mx));}),_oe=new T(function(){return B(A1(_nP,_mr));}),_of=new T(function(){return B(A1(_nP,_ml));}),_og=new T(function(){return B(A1(_nP,_mf));}),_oh=new T(function(){return B(A1(_nP,_m9));}),_oi=new T(function(){return B(A1(_nP,_m3));}),_oj=new T(function(){return B(A1(_nP,_lX));}),_ok=new T(function(){return B(A1(_nP,_lR));}),_ol=new T(function(){return B(A1(_nP,_lL));}),_om=new T(function(){return B(A1(_nP,_lF));}),_on=new T(function(){return B(A1(_nP,_lz));}),_oo=new T(function(){return B(A1(_nP,_lt));}),_op=new T(function(){return B(A1(_nP,_ln));}),_oq=new T(function(){return B(A1(_nP,_jT));}),_or=new T(function(){return B(A1(_nP,_kB));}),_os=new T(function(){return B(A1(_nP,_kv));}),_ot=new T(function(){return B(A1(_nP,_kp));}),_ou=new T(function(){return B(A1(_nP,_kj));}),_ov=new T(function(){return B(A1(_nP,_kd));}),_ow=new T(function(){return B(A1(_nP,_jZ));}),_ox=new T(function(){return B(A1(_nP,_k7));}),_oy=function(_oz){switch(E(_oz)){case 64:return E(_ox);case 65:return E(_ow);case 66:return E(_ov);case 67:return E(_ou);case 68:return E(_ot);case 69:return E(_os);case 70:return E(_or);case 71:return E(_nQ);case 72:return E(_nR);case 73:return E(_nS);case 74:return E(_nT);case 75:return E(_nU);case 76:return E(_nV);case 77:return E(_nW);case 78:return E(_oq);case 79:return E(_op);case 80:return E(_oo);case 81:return E(_on);case 82:return E(_om);case 83:return E(_ol);case 84:return E(_ok);case 85:return E(_oj);case 86:return E(_oi);case 87:return E(_oh);case 88:return E(_og);case 89:return E(_of);case 90:return E(_oe);case 91:return E(_od);case 92:return E(_oc);case 93:return E(_ob);case 94:return E(_oa);case 95:return E(_o9);default:return new T0(2);}};return B(_eG(new T1(0,function(_oA){return (E(_oA)==94)?E(new T1(0,_oy)):new T0(2);}),new T(function(){return B(A1(_nJ,_nP));})));});return B(_eG(new T1(1,B(_fS(_jh,_jj,_o1))),_o8));});return new F(function(){return _eG(new T1(0,function(_oB){switch(E(_oB)){case 34:return E(_nZ);case 39:return E(_nY);case 92:return E(_nX);case 97:return E(_nQ);case 98:return E(_nR);case 102:return E(_nV);case 110:return E(_nT);case 114:return E(_nW);case 116:return E(_nS);case 118:return E(_nU);default:return new T0(2);}}),_o0);});},_oC=function(_oD){return new F(function(){return A1(_oD,_43);});},_oE=function(_oF){var _oG=E(_oF);if(!_oG._){return E(_oC);}else{var _oH=E(_oG.a),_oI=_oH>>>0,_oJ=new T(function(){return B(_oE(_oG.b));});if(_oI>887){var _oK=u_iswspace(_oH);if(!E(_oK)){return E(_oC);}else{var _oL=function(_oM){var _oN=new T(function(){return B(A1(_oJ,_oM));});return new T1(0,function(_oO){return E(_oN);});};return E(_oL);}}else{var _oP=E(_oI);if(_oP==32){var _oQ=function(_oR){var _oS=new T(function(){return B(A1(_oJ,_oR));});return new T1(0,function(_oT){return E(_oS);});};return E(_oQ);}else{if(_oP-9>>>0>4){if(E(_oP)==160){var _oU=function(_oV){var _oW=new T(function(){return B(A1(_oJ,_oV));});return new T1(0,function(_oX){return E(_oW);});};return E(_oU);}else{return E(_oC);}}else{var _oY=function(_oZ){var _p0=new T(function(){return B(A1(_oJ,_oZ));});return new T1(0,function(_p1){return E(_p0);});};return E(_oY);}}}}},_p2=function(_p3){var _p4=new T(function(){return B(_p2(_p3));}),_p5=function(_p6){return (E(_p6)==92)?E(_p4):new T0(2);},_p7=function(_p8){return E(new T1(0,_p5));},_p9=new T1(1,function(_pa){return new F(function(){return A2(_oE,_pa,_p7);});}),_pb=new T(function(){return B(_nO(function(_pc){return new F(function(){return A1(_p3,new T2(0,_pc,_jb));});}));}),_pd=function(_pe){var _pf=E(_pe);if(_pf==38){return E(_p4);}else{var _pg=_pf>>>0;if(_pg>887){var _ph=u_iswspace(_pf);return (E(_ph)==0)?new T0(2):E(_p9);}else{var _pi=E(_pg);return (_pi==32)?E(_p9):(_pi-9>>>0>4)?(E(_pi)==160)?E(_p9):new T0(2):E(_p9);}}};return new F(function(){return _eG(new T1(0,function(_pj){return (E(_pj)==92)?E(new T1(0,_pd)):new T0(2);}),new T1(0,function(_pk){var _pl=E(_pk);if(E(_pl)==92){return E(_pb);}else{return new F(function(){return A1(_p3,new T2(0,_pl,_ja));});}}));});},_pm=function(_pn,_po){var _pp=new T(function(){return B(A1(_po,new T1(1,new T(function(){return B(A1(_pn,_v));}))));}),_pq=function(_pr){var _ps=E(_pr),_pt=E(_ps.a);if(E(_pt)==34){if(!E(_ps.b)){return E(_pp);}else{return new F(function(){return _pm(function(_pu){return new F(function(){return A1(_pn,new T2(1,_pt,_pu));});},_po);});}}else{return new F(function(){return _pm(function(_pv){return new F(function(){return A1(_pn,new T2(1,_pt,_pv));});},_po);});}};return new F(function(){return _p2(_pq);});},_pw=new T(function(){return B(unCStr("_\'"));}),_px=function(_py){var _pz=u_iswalnum(_py);if(!E(_pz)){return new F(function(){return _6N(_6K,_py,_pw);});}else{return true;}},_pA=function(_pB){return new F(function(){return _px(E(_pB));});},_pC=new T(function(){return B(unCStr(",;()[]{}`"));}),_pD=new T(function(){return B(unCStr("=>"));}),_pE=new T2(1,_pD,_v),_pF=new T(function(){return B(unCStr("~"));}),_pG=new T2(1,_pF,_pE),_pH=new T(function(){return B(unCStr("@"));}),_pI=new T2(1,_pH,_pG),_pJ=new T(function(){return B(unCStr("->"));}),_pK=new T2(1,_pJ,_pI),_pL=new T(function(){return B(unCStr("<-"));}),_pM=new T2(1,_pL,_pK),_pN=new T(function(){return B(unCStr("|"));}),_pO=new T2(1,_pN,_pM),_pP=new T(function(){return B(unCStr("\\"));}),_pQ=new T2(1,_pP,_pO),_pR=new T(function(){return B(unCStr("="));}),_pS=new T2(1,_pR,_pQ),_pT=new T(function(){return B(unCStr("::"));}),_pU=new T2(1,_pT,_pS),_pV=new T(function(){return B(unCStr(".."));}),_pW=new T2(1,_pV,_pU),_pX=function(_pY){var _pZ=new T(function(){return B(A1(_pY,_gw));}),_q0=new T(function(){var _q1=new T(function(){var _q2=function(_q3){var _q4=new T(function(){return B(A1(_pY,new T1(0,_q3)));});return new T1(0,function(_q5){return (E(_q5)==39)?E(_q4):new T0(2);});};return B(_nO(_q2));}),_q6=function(_q7){var _q8=E(_q7);switch(E(_q8)){case 39:return new T0(2);case 92:return E(_q1);default:var _q9=new T(function(){return B(A1(_pY,new T1(0,_q8)));});return new T1(0,function(_qa){return (E(_qa)==39)?E(_q9):new T0(2);});}},_qb=new T(function(){var _qc=new T(function(){return B(_pm(_3h,_pY));}),_qd=new T(function(){var _qe=new T(function(){var _qf=new T(function(){var _qg=function(_qh){var _qi=E(_qh),_qj=u_iswalpha(_qi);return (E(_qj)==0)?(E(_qi)==95)?new T1(1,B(_gi(_pA,function(_qk){return new F(function(){return A1(_pY,new T1(3,new T2(1,_qi,_qk)));});}))):new T0(2):new T1(1,B(_gi(_pA,function(_ql){return new F(function(){return A1(_pY,new T1(3,new T2(1,_qi,_ql)));});})));};return B(_eG(new T1(0,_qg),new T(function(){return new T1(1,B(_fS(_hu,_j5,_pY)));})));}),_qm=function(_qn){return (!B(_6N(_6K,_qn,_j7)))?new T0(2):new T1(1,B(_gi(_j8,function(_qo){var _qp=new T2(1,_qn,_qo);if(!B(_6N(_fx,_qp,_pW))){return new F(function(){return A1(_pY,new T1(4,_qp));});}else{return new F(function(){return A1(_pY,new T1(2,_qp));});}})));};return B(_eG(new T1(0,_qm),_qf));});return B(_eG(new T1(0,function(_qq){if(!B(_6N(_6K,_qq,_pC))){return new T0(2);}else{return new F(function(){return A1(_pY,new T1(2,new T2(1,_qq,_v)));});}}),_qe));});return B(_eG(new T1(0,function(_qr){return (E(_qr)==34)?E(_qc):new T0(2);}),_qd));});return B(_eG(new T1(0,function(_qs){return (E(_qs)==39)?E(new T1(0,_q6)):new T0(2);}),_qb));});return new F(function(){return _eG(new T1(1,function(_qt){return (E(_qt)._==0)?E(_pZ):new T0(2);}),_q0);});},_qu=0,_qv=function(_qw,_qx){var _qy=new T(function(){var _qz=new T(function(){var _qA=function(_qB){var _qC=new T(function(){var _qD=new T(function(){return B(A1(_qx,_qB));});return B(_pX(function(_qE){var _qF=E(_qE);return (_qF._==2)?(!B(_fk(_qF.a,_fj)))?new T0(2):E(_qD):new T0(2);}));}),_qG=function(_qH){return E(_qC);};return new T1(1,function(_qI){return new F(function(){return A2(_oE,_qI,_qG);});});};return B(A2(_qw,_qu,_qA));});return B(_pX(function(_qJ){var _qK=E(_qJ);return (_qK._==2)?(!B(_fk(_qK.a,_fi)))?new T0(2):E(_qz):new T0(2);}));}),_qL=function(_qM){return E(_qy);};return function(_qN){return new F(function(){return A2(_oE,_qN,_qL);});};},_qO=function(_qP,_qQ){var _qR=function(_qS){var _qT=new T(function(){return B(A1(_qP,_qS));}),_qU=function(_qV){return new F(function(){return _eG(B(A1(_qT,_qV)),new T(function(){return new T1(1,B(_qv(_qR,_qV)));}));});};return E(_qU);},_qW=new T(function(){return B(A1(_qP,_qQ));}),_qX=function(_qY){return new F(function(){return _eG(B(A1(_qW,_qY)),new T(function(){return new T1(1,B(_qv(_qR,_qY)));}));});};return E(_qX);},_qZ=function(_r0,_r1){var _r2=function(_r3,_r4){var _r5=function(_r6){return new F(function(){return A1(_r4,new T(function(){return  -E(_r6);}));});},_r7=new T(function(){return B(_pX(function(_r8){return new F(function(){return A3(_r0,_r8,_r3,_r5);});}));}),_r9=function(_ra){return E(_r7);},_rb=function(_rc){return new F(function(){return A2(_oE,_rc,_r9);});},_rd=new T(function(){return B(_pX(function(_re){var _rf=E(_re);if(_rf._==4){var _rg=E(_rf.a);if(!_rg._){return new F(function(){return A3(_r0,_rf,_r3,_r4);});}else{if(E(_rg.a)==45){if(!E(_rg.b)._){return E(new T1(1,_rb));}else{return new F(function(){return A3(_r0,_rf,_r3,_r4);});}}else{return new F(function(){return A3(_r0,_rf,_r3,_r4);});}}}else{return new F(function(){return A3(_r0,_rf,_r3,_r4);});}}));}),_rh=function(_ri){return E(_rd);};return new T1(1,function(_rj){return new F(function(){return A2(_oE,_rj,_rh);});});};return new F(function(){return _qO(_r2,_r1);});},_rk=function(_rl){var _rm=E(_rl);if(!_rm._){var _rn=_rm.b,_ro=new T(function(){return B(_ih(new T(function(){return B(_hX(E(_rm.a)));}),new T(function(){return B(_hS(_rn,0));},1),B(_60(_hZ,_rn))));});return new T1(1,_ro);}else{return (E(_rm.b)._==0)?(E(_rm.c)._==0)?new T1(1,new T(function(){return B(_iy(_hR,_rm.a));})):__Z:__Z;}},_rp=function(_rq,_rr){return new T0(2);},_rs=function(_rt){var _ru=E(_rt);if(_ru._==5){var _rv=B(_rk(_ru.a));if(!_rv._){return E(_rp);}else{var _rw=new T(function(){return B(_jl(_rv.a));});return function(_rx,_ry){return new F(function(){return A1(_ry,_rw);});};}}else{return E(_rp);}},_rz=function(_rA){var _rB=function(_rC){return E(new T2(3,_rA,_fJ));};return new T1(1,function(_rD){return new F(function(){return A2(_oE,_rD,_rB);});});},_rE=new T(function(){return B(A3(_qZ,_rs,_qu,_rz));}),_rF=new T(function(){return B(_48(_41,_7l));}),_rG=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:46:36-46"));}),_rH=new T6(0,_2q,_2r,_v,_rG,_2q,_2q),_rI=new T(function(){return B(_2o(_rH));}),_rJ=function(_rK){while(1){var _rL=B((function(_rM){var _rN=E(_rM);if(!_rN._){return __Z;}else{var _rO=_rN.b,_rP=E(_rN.a);if(!E(_rP.b)._){return new T2(1,_rP.a,new T(function(){return B(_rJ(_rO));}));}else{_rK=_rO;return __continue;}}})(_rK));if(_rL!=__continue){return _rL;}}},_rQ=function(_rR,_rS,_){var _rT=E(_rS);if(!_rT._){return _43;}else{var _rU=E(_7S),_rV=E(_8r),_rW=__app1(_rV,toJSStr(_rU)),_rX=_rW,_rY=B(A1(_rF,_)),_rZ=E(_rY);if(!_rZ._){return new F(function(){return die(_rI);});}else{var _s0=E(_5g),_s1=E(_7E),_s2=__app3(_s1,_rX,toJSStr(_s0),toJSStr(B(_d(0,_rR,_v)))),_s3=E(_7H),_s4=E(_a4),_s5=__app3(_s4,_rX,toJSStr(_s3),true),_s6=E(_7G),_s7=__app3(_s4,_rX,toJSStr(_s6),true),_s8=B(A(_9C,[_42,_3j,_3e,_rX,_44,function(_s9,_){var _sa=B(A(_56,[_3j,_41,_rX,_s0,_])),_sb=E(_sa);if(!_sb._){return new F(function(){return _a5(E(_dv).b,_);});}else{var _sc=B(_rJ(B(_ew(_rE,_sb))));if(!_sc._){return E(_dx);}else{if(!E(_sc.b)._){return new F(function(){return _a5(B(_7y(_du,E(_sc.a))).b,_);});}else{return E(_dz);}}}},_])),_sd=E(_dv).b,_se=B(_a5(_sd,_)),_sf=E(_7B),_sg=__app2(_sf,_rX,E(_rZ.a)),_sh=E(_9q),_si=__app1(_sh,toJSStr(E(E(_rT.a).a))),_sj=__app2(_sf,_si,_rX),_sk=E(_rR);if(_sk==2147483647){return _43;}else{var _sl=function(_sm,_sn,_){while(1){var _so=B((function(_sp,_sq,_){var _sr=E(_sq);if(!_sr._){return _43;}else{var _ss=__app1(_rV,toJSStr(_rU)),_st=_ss,_su=B(A1(_rF,_)),_sv=E(_su);if(!_sv._){return new F(function(){return die(_rI);});}else{var _sw=__app3(_s1,_st,toJSStr(_s0),toJSStr(B(_d(0,_sp,_v)))),_sx=__app3(_s4,_st,toJSStr(_s3),true),_sy=__app3(_s4,_st,toJSStr(_s6),true),_sz=B(A(_9C,[_42,_3j,_3e,_st,_44,function(_sA,_){var _sB=B(A(_56,[_3j,_41,_st,_s0,_])),_sC=E(_sB);if(!_sC._){return new F(function(){return _a5(_sd,_);});}else{var _sD=B(_rJ(B(_ew(_rE,_sC))));if(!_sD._){return E(_dx);}else{if(!E(_sD.b)._){return new F(function(){return _a5(B(_7y(_du,E(_sD.a))).b,_);});}else{return E(_dz);}}}},_])),_sE=B(_a5(_sd,_)),_sF=__app2(_sf,_st,E(_sv.a)),_sG=__app1(_sh,toJSStr(E(E(_sr.a).a))),_sH=__app2(_sf,_sG,_st),_sI=E(_sp);if(_sI==2147483647){return _43;}else{_sm=_sI+1|0;_sn=_sr.b;return __continue;}}}})(_sm,_sn,_));if(_so!=__continue){return _so;}}};return new F(function(){return _sl(_sk+1|0,_rT.b,_);});}}}},_sJ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:101:31-41"));}),_sK=new T6(0,_2q,_2r,_v,_sJ,_2q,_2q),_sL=new T(function(){return B(_2o(_sK));}),_sM=new T(function(){return B(unCStr("No Solution!"));}),_sN=function(_sO,_sP,_sQ){var _sR=E(_sQ);if(!_sR._){return __Z;}else{var _sS=_sR.a,_sT=_sR.b;return (!B(A2(_sO,_sP,_sS)))?new T2(1,_sS,new T(function(){return B(_sN(_sO,_sP,_sT));})):E(_sT);}},_sU=function(_sV,_sW,_sX){return new F(function(){return _sN(new T(function(){return B(_6L(_sV));}),_sW,_sX);});},_sY=function(_sZ,_t0,_t1){var _t2=function(_t3,_t4){while(1){var _t5=E(_t3);if(!_t5._){return E(_t4);}else{var _t6=B(_sU(_sZ,_t5.a,_t4));_t3=_t5.b;_t4=_t6;continue;}}};return new F(function(){return _t2(_t1,_t0);});},_t7=function(_t8){while(1){var _t9=B((function(_ta){var _tb=E(_ta);if(!_tb._){return __Z;}else{var _tc=_tb.b,_td=E(_tb.a);if(!_td._){_t8=_tc;return __continue;}else{if(!E(_td.b)._){return new F(function(){return _3(_td,new T(function(){return B(_t7(_tc));},1));});}else{_t8=_tc;return __continue;}}}})(_t8));if(_t9!=__continue){return _t9;}}},_te=function(_tf){var _tg=new T(function(){return B(_t7(_tf));}),_th=new T(function(){return B(_sY(_6K,_v,_tg));}),_ti=function(_tj){var _tk=E(_tj);return (_tk._==0)?__Z:new T2(1,new T(function(){var _tl=E(_tk.a);if(!_tl._){return E(_th);}else{if(!E(_tl.b)._){return E(_tl);}else{return B(_sY(_6K,_tl,_tg));}}}),new T(function(){return B(_ti(_tk.b));}));};return new F(function(){return _ti(_tf);});},_tm=function(_tn,_to){var _tp=E(_to);if(!_tp._){return new T2(0,_v,_v);}else{var _tq=_tp.a;if(!B(A1(_tn,_tq))){var _tr=new T(function(){var _ts=B(_tm(_tn,_tp.b));return new T2(0,_ts.a,_ts.b);});return new T2(0,new T2(1,_tq,new T(function(){return E(E(_tr).a);})),new T(function(){return E(E(_tr).b);}));}else{return new T2(0,_v,_tp);}}},_tt=function(_tu){while(1){var _tv=E(_tu);if(!_tv._){return false;}else{var _tw=E(_tv.a);if(!_tw._){return true;}else{if(!E(_tw.b)._){_tu=_tv.b;continue;}else{return true;}}}}},_tx=function(_ty){return new F(function(){return _tt(_ty);});},_tz=new T2(1,_v,_v),_tA=function(_tB){var _tC=E(_tB);if(!_tC._){return E(_tz);}else{var _tD=new T(function(){return B(_tA(_tC.b));}),_tE=function(_tF){var _tG=E(_tF);if(!_tG._){return __Z;}else{var _tH=new T(function(){return B(_tE(_tG.b));}),_tI=function(_tJ){var _tK=E(_tJ);return (_tK._==0)?E(_tH):new T2(1,new T2(1,_tG.a,_tK.a),new T(function(){return B(_tI(_tK.b));}));};return new F(function(){return _tI(_tD);});}};return new F(function(){return _tE(_tC.a);});}},_tL=function(_tM){while(1){var _tN=E(_tM);if(!_tN._){return true;}else{var _tO=E(_tN.a);if(!_tO._){return false;}else{if(!E(_tO.b)._){_tM=_tN.b;continue;}else{return false;}}}}},_tP=function(_tQ){while(1){var _tR=E(_tQ);if(!_tR._){return true;}else{if(!B(_tL(_tR.a))){return false;}else{_tQ=_tR.b;continue;}}}},_tS=function(_tT){while(1){var _tU=B((function(_tV){var _tW=E(_tV);if(!_tW._){return __Z;}else{var _tX=_tW.b,_tY=E(_tW.a);if(!_tY._){_tT=_tX;return __continue;}else{if(!E(_tY.b)._){return new F(function(){return _3(_tY,new T(function(){return B(_tS(_tX));},1));});}else{_tT=_tX;return __continue;}}}})(_tT));if(_tU!=__continue){return _tU;}}},_tZ=function(_u0){while(1){var _u1=E(_u0);if(!_u1._){return true;}else{if(!B(_6S(B(_tS(_u1.a))))){return false;}else{_u0=_u1.b;continue;}}}},_u2=function(_u3){while(1){var _u4=E(_u3);if(!_u4._){return true;}else{if(!B(_6S(B(_tS(_u4.a))))){return false;}else{_u3=_u4.b;continue;}}}},_u5=function(_u6){while(1){var _u7=E(_u6);if(!_u7._){return true;}else{if(!B(_6S(B(_tS(_u7.a))))){return false;}else{_u6=_u7.b;continue;}}}},_u8=function(_u9){while(1){var _ua=E(_u9);if(!_ua._){return false;}else{if(!E(_ua.a)._){return true;}else{_u9=_ua.b;continue;}}}},_ub=function(_uc){while(1){var _ud=E(_uc);if(!_ud._){return false;}else{if(!B(_u8(_ud.a))){_uc=_ud.b;continue;}else{return true;}}}},_ue=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_uf=function(_ug){return new F(function(){return _e4(new T1(0,new T(function(){return B(_ei(_ug,_ue));})),_dO);});},_uh=new T(function(){return B(_uf("Solution.hs:186:7-50|(row1, cs : row2)"));}),_ui=function(_uj){var _uk=E(_uj);return (_uk._==0)?true:(E(_uk.b)._==0)?false:true;},_ul=new T(function(){return B(_uf("Solution.hs:185:7-54|(rows1, row : rows2)"));}),_um=function(_un,_uo,_up){var _uq=E(_un);if(_uq==1){return E(_up);}else{return new F(function(){return _5I(_uq-1|0,_up);});}},_ur=function(_us,_ut,_uu){return new T2(1,new T(function(){if(0>=_us){return __Z;}else{return B(_5O(_us,new T2(1,_ut,_uu)));}}),new T(function(){if(_us>0){return B(_uv(_us,B(_um(_us,_ut,_uu))));}else{return B(_ur(_us,_ut,_uu));}}));},_uv=function(_uw,_ux){var _uy=E(_ux);if(!_uy._){return __Z;}else{var _uz=_uy.a,_uA=_uy.b;return new T2(1,new T(function(){if(0>=_uw){return __Z;}else{return B(_5O(_uw,_uy));}}),new T(function(){if(_uw>0){return B(_uv(_uw,B(_um(_uw,_uz,_uA))));}else{return B(_ur(_uw,_uz,_uA));}}));}},_uB=function(_uC){return new F(function(){return _69(B(_60(_6w,B(_uv(3,B(_60(_6g,B(_60(_te,B(_69(B(_60(_6w,B(_uv(3,B(_60(_6g,_uC)))))))))))))))));});},_uD=function(_uE){if(!B(_ub(_uE))){if(!B(_u5(_uE))){return __Z;}else{if(!B(_u2(B(_6w(_uE))))){return __Z;}else{if(!B(_tZ(B(_69(B(_60(_6w,B(_uv(3,B(_60(_6g,_uE))))))))))){return __Z;}else{if(!B(_tP(_uE))){var _uF=B(_tm(_tx,_uE)),_uG=E(_uF.b);if(!_uG._){return E(_ul);}else{var _uH=B(_tm(_ui,_uG.a)),_uI=E(_uH.b);if(!_uI._){return E(_uh);}else{var _uJ=new T(function(){return B(_60(_te,_uG.b));}),_uK=function(_uL){var _uM=E(_uL);if(!_uM._){return __Z;}else{var _uN=new T(function(){return B(_te(B(_3(_uH.a,new T2(1,new T2(1,_uM.a,_v),_uI.b)))));}),_uO=function(_uP){var _uQ=E(_uP);return (_uQ._==0)?E(new T2(1,_uN,_uJ)):new T2(1,new T(function(){return B(_te(_uQ.a));}),new T(function(){return B(_uO(_uQ.b));}));};return new F(function(){return _3(B(_uD(B(_uB(B(_6w(B(_60(_te,B(_6w(B(_uO(_uF.a)))))))))))),new T(function(){return B(_uK(_uM.b));},1));});}};return new F(function(){return _uK(_uI.a);});}}}else{return new F(function(){return _tA(B(_60(_tA,_uE)));});}}}}}else{return __Z;}},_uR=function(_uS,_uT){return (_uS<=_uT)?new T2(1,_uS,new T(function(){return B(_uR(_uS+1|0,_uT));})):__Z;},_uU=new T(function(){return B(_uR(49,57));}),_uV=function(_uW){var _uX=E(_uW);return (E(_uX)==46)?E(_uU):new T2(1,_uX,_v);},_uY=function(_uZ){return new F(function(){return _te(B(_60(_uV,_uZ)));});},_v0=function(_v1){return new F(function(){return _uD(B(_uB(B(_6w(B(_60(_te,B(_6w(B(_60(_uY,_v1)))))))))));});},_v2=function(_v3,_){var _v4=B(_5w(_4M,_)),_v5=B(_v0(_v4));if(!_v5._){var _v6=B(A3(_4j,_41,_sM,_));return _43;}else{var _v7=B(A1(_9p,_)),_v8=E(_v7);if(!_v8._){return new F(function(){return die(_sL);});}else{var _v9=E(_v8.a),_va=__app1(E(_7C),_v9),_vb=B(_8w(_v9,_v5.a,_));return _43;}}},_vc=function(_){var _vd=B(_rQ(0,_du,_)),_ve=B(A3(_48,_41,_7l,_));if(!E(_ve)._){return new F(function(){return die(_7k);});}else{var _vf=B(A3(_48,_41,_7h,_)),_vg=E(_vf);if(!_vg._){return new F(function(){return die(_7g);});}else{var _vh=B(A3(_48,_41,_7d,_)),_vi=E(_vh);if(!_vi._){return new F(function(){return die(_4g);});}else{var _vj=B(A(_9C,[_42,_3j,_3e,_vg.a,_44,_v2,_])),_vk=B(A(_9C,[_42,_3j,_3e,_vi.a,_44,_77,_]));return _43;}}}},_vl=function(_){return new F(function(){return _vc(_);});};
var hasteMain = function() {B(A(_vl, [0]));};window.onload = hasteMain;