/*
 * Class Kernel - v1.0 - 2014.12.06
 * 
 * Francois Marie De Mey <eeddow@gmail.com>
 * License: GPL / tl;dr: DON'T BE AN ASS.
 * - Change, publish, use at leisure, even for profit - but refer the real author
 * - The code comes with no warranty of any kind: The author declines any responsability in anything, from data loss to kitty death
 */
window.classy = (function() {
	var classCounter = 0, rootObject = {};
	Object.defineProperty(rootObject, 'legacy', {
		enumerable: false,
		get: function() {
			var me= this, f = arguments.callee.caller, chain = f.caller.parent, called;
			if(chain) {
				called = chain.original||chain;
				return dob=ext(function() { return called.apply(me, arguments); }, {
					parent: chain.parent,
					chain: ext(function() {
						var args = [].slice.call(arguments, 0);
						return called.apply(me, args.concat([].slice.call(f.arguments, args.length)));
					}, {parent: chain.parent}),
					apply: ext(function(args) { return called.apply(me, args); }, {parent: chain.parent})
				});
			}
			return classy.emptyLegacy;
		}
	});
	function setMbrs(obj, mbrs) {
		if(!mbrs) return;
		var i, oFcts, mFcts;
		function pairGetSet(name, originalValue, todos) {
			var rv = {
				set: todos.set&&todos.get?function(v) { return originalValue = v; }:false,
				get: todos.get?(function() { return originalValue; }):false
			};
			if(rv.set) rv.set.terminal;
			if(rv.get) rv.get.terminal;
			return rv;
		}
		function addLegacy(fct, last) {
			while(fct.parent) {
				fct = fct.parent;
				if(fct.isTerminal) return;
			}
			Object.defineProperty(fct, 'parent', {
				value: last,
				writable: false,
				configurable: false
			});
		}
		function cloneFct(original, name) {
			if(!original) return;
			var Classy;
			Classy = 'constructor'=== name?
				function() { ++this.__constructorCalled__; return original.apply(this, arguments); }:
				function() { return original.apply(this, arguments); };
			Object.defineProperty(Classy, 'original', {
				value: original,
				writable: false,
				configurable: false
			});
			return Classy;
		}
		function lookups(itm) {
			var rv = {
				get: itm.__lookupGetter__(i),
				set: itm.__lookupSetter__(i)
			};
			if(rv.get || rv.set) return rv;
		}
		
		for(i in mbrs) {
			oFcts = lookups(obj);
			mFcts = lookups(mbrs);
		
			if(oFcts && !mFcts) {
				mFcts = pairGetSet(i, mbrs[i], oFcts);
			} else if(mFcts) {
				mFcts.get = cloneFct(mFcts.get, 'get_i');
				mFcts.set = cloneFct(mFcts.set, 'set_i');
				if(!oFcts) {
					//if the object already has a property, tyhe property overrides the get/set from mbrs
					//if not, we just forward the get/set
					if(obj.hasOwnProperty(i)) mFcts = false;
					else oFcts = {get: false, set: false};
				}
			}
			
			if(mFcts) {
				if(mFcts.get) {
					if(oFcts.get) addLegacy(oFcts.get, mFcts.get);
					else obj.__defineGetter__(i, mFcts.get);
				} if(mFcts.set) {
					if(oFcts.set) addLegacy(oFcts.set, mFcts.set);
					else obj.__defineSetter__(i, mFcts.set);
				}
			} else {
				if(mFcts = ('function'=== typeof mbrs[i]))
					oFcts = cloneFct(mbrs[i], i);
				else oFcts = mbrs[i];

//TODO: when .get returns a function and this function calls its legacy
				if(obj.hasOwnProperty(i)) {
					if(mFcts ^ ('function'=== typeof obj[i]))
						throw new classy.exception('Member "'+i+'" is heritated - once a function once not');
					if(mFcts) addLegacy(obj[i], oFcts);
				} else obj[i] = oFcts;
			}
		}
	}
	function ext(dst) {
		var i, j, args = arguments, obj;
		for(i = 1; i<args.length; ++i)
			for(j in obj = args[i])
				if(obj.hasOwnProperty(j))
					dst[j] = obj[j];
		return dst;
	}
	ext(Function.prototype, { get terminal() { this.isTerminal = true; return this; } });
	
	classy = ext(function(members) {
		var rv = false,
			xtnds = [].slice.call(arguments, 1), mFleg=[], orders = {}, i, j,
			waitings = {}, ready = 'me', classes = {}, orgCtor, cname;
		//rv -> {cidA: {cidB: true (A before B)} }
		//classes -> {cid: class object}
		function order(rv, classes, list, before, inheriting) {
			var i, j, clss, len;
			function precede(a, b, force) {
				rv[a] || (rv[a] = {});
				rv[b] || (rv[b] = {});
				if(!rv[b][a])
					rv[a][b] = true;
				else if(force) {
					rv[a][b] = true;
					delete rv[b][a];
				}
			}
			for(i=0; i<list.length; ++i) {
				clss = list[i];
				classes[clss.cid] = clss;
				for(j=0; j< inheriting.length; ++j) {
					if(inheriting[j] === clss.cid) throw new classy.exception('Cycle in inheritance');
					precede(inheriting[j], clss.cid, true);
				}
				len = before.length;
				before.push(clss);
				for(j=0; j< len; ++j) {
					if(before[j] === clss) before.pop();
					else precede(before[j].cid, clss.cid, false);
				}
				if(clss.inherits.length) {
					inheriting.push(clss.cid);
					order(rv, classes, clss.inherits, before, inheriting);
					inheriting.pop();
				}
			}
		}
		order(orders, classes, xtnds, [], [ready]);
		for(i in orders.me) waitings[i] = 0;
		for(i in orders) for(j in orders[i]) ++waitings[j];
		while(ready) {
			j = ready;
			ready = false;
			for(i in orders[j]) {
				if(!--waitings[i]) {
					//@ assert Order is perfect, there is one ready at a time : !ready
					ready = i;
				}
			}
			if(ready) mFleg.push(classes[ready]);
		}
		//todo: assert \/x, !waitings[x]

		members || (members = {});
		if({}.constructor=== members.constructor) members.constructor = (function() {});
		rv = Object.create(rootObject);
		setMbrs(rv, members);
		for(i = 0; i< mFleg.length; ++i)
			setMbrs(rv, mFleg[i].members);
		orgCtor = rv.constructor;
		function ctor() {
			var me=this, ctr = orgCtor, constructorCalled, nctor;
			ctr = nctor = ext((function(original) {
				return function() { ++constructorCalled; return original.apply(this, arguments); };
			})(ctr.original), {
				parent: ctr.parent,
				original: ctr.original
			});
			while(ctr.parent) {
				ctr = ctr.parent = ext((function(original) {
					return function() { ++constructorCalled; return original.apply(this, arguments); };
				})(ctr.parent.original), {
				parent: ctr.parent.parent,
				original: ctr.parent.original
			});
			}
			ctr = nctor;
			while(ctr) {
				constructorCalled = 0;
				ctr.apply(me, arguments);
				while(constructorCalled--) ctr = ctr.parent;
			}
			delete constructorCalled;
		};
		cname = members.constructor.name || 'ClassyObject';
		rv.constructor = eval('[function '+cname+'() { return ctor.apply(this, arguments); }]')[0];
		Object.defineProperty(rv, 'constructor', {
			enumerable: false,
			writable: false,
			configurable: false
		});
		return ext(
			rv.constructor,
			{
				constructor: classy,
				prototype: rv,
				inherits: Object.freeze(xtnds),
				members: Object.freeze(members),
				fleg: Object.freeze(mFleg),
				cid: ++classCounter,
				classify: function(obj) {
					var me= this, ctr = obj.constructor;
					return me === ctr || 0<= ctr.fleg.indexOf(me);
				},
				extends: function(parent) {
					return 0<= this.fleg.indexOf(parent);
				},
				toString: function() {
					return '[class'+(cname?' '+cname:'')+']';
				}
			}
		);
	}, {
		emptyLegacy: ext(function() {}, {
			chain: function() {},
			apply: function() {}
		}),
		exception: function(msg) {
			this.message = msg;
		},
		singleton: ext(function(members) {
			var obj, xtnds = [].slice.call(arguments, 1), classes, mClass, i;
			members || (members = {});
			classes = [members];
			for(i=0; i<xtnds.length; ++i)
				classes.push(classy=== xtnds[i].constructor?xtnds[i]:xtnds[i].constructor);
			mClass = classy.apply(this, classes);
			fleg = mClass.fleg;
			obj = new mClass();
			return obj;
		}, {
			extendedMember: function(me, mbrName) {
				if(!(mbrName instanceof Array)) mbrName = [].slice.call(arguments, 1);
				var i, j, mbr, fleg = me.constructor.fleg, rv;
				for(i=0; i< mbrName.length; ++i) {
					rv = {};
					mbr = mbrName[i];
					setMbrs(rv, me[mbr]);
					for(j = 0; j< fleg.length; ++j)
						setMbrs(rv, fleg[j].members[mbr]);
					me[mbr] = rv || {};
				}
			}
		})
	});
	classy.class = classy;
	return classy;
})();
