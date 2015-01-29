/*
 * Class Kernel - v1.0 - 2014.12.10
 * 
 * Francois Marie De Mey <eeddow@gmail.com>
 * License: GPL / tl;dr: DON'T BE AN ARSE - Be fair
 * - Change, publish, use at leisure - but refer the real author
 * - The code comes with no warranty of any kind: The author declines any responsability in anything, from data loss to kitten death
 */
window.classy = (function() {
	function ext(dst) {
		var i, j, args = arguments, obj;
		for(i = 1; i<args.length; ++i)
			for(j in obj = args[i])
				if(obj.hasOwnProperty(j))
					dst[j] = obj[j];
		return dst;
	}
	//Little-Endian Base64
	function nextLEB64(s) {
		var rv = '', tval = 0;
		while(0=== tval && ''!== s) {
			rv += base64[tval = (1+base64.indexOf(s[0])) & 63];
			s = s.substr(1);
		}
		if(0=== tval) return rv+base64[0];
		return rv+s;
	}
	function idSpace(name) {
		var value = '';
		this.name = name||'someIdSpace';
		this.next = function() {
			return value = nextLEB64(value);
		};
	}
	idSpace.prototype = {
		toString: function() { return this.name; }
	};
	var base64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_',
		classCounter = new idSpace('classyClassCounter'), objectCounter = new idSpace('classyObjectCounter'),
		rootObject = {}, getSetCache = {}, constructorCalled = {};
	Object.defineProperty(rootObject, 'legacy', {
		enumerable: false,
		writable: false,
		configurable: false,
		value: function ClassyLegacy(args) {
			var me= this, f = arguments.callee.caller, chain = f.caller;
			if(chain) {
				chain = chain.parent;
				if(chain) {
					if(args && Array!== args.constructor) {
						args = [].slice.call(arguments, 1);
						args = args.concat([].slice.call(f.arguments, args.length));
					}
					return chain.apply(me, args||f.arguments);
				}
			}
		}
	});
	function setMbrs(obj, mbrs) {
		if(!mbrs) return;
		var i, oFcts, mFcts;
		function pairGetSet(name, originalValue, todos) {
			var rv = {
					set: todos.set&&todos.get?function ClassyCacheSet(v) {
						var uid= this.oid;
						getSetCache[uid] || (getSetCache[uid]={});
						getSetCache[uid][name] = v;
					}:false,
					get: todos.get?(
						todos.set?
						function ClassyCacheGet() {
							var cached = getSetCache[this.oid];
							return cached && cached.hasOwnProperty(name)?cached[name]:originalValue;
						}:
						function ClassyCacheSet() { return originalValue; }
					):false
			};
			if(rv.set) rv.set.terminal = true;
			if(rv.get) rv.get.terminal = true;
			return rv;
		}
		function addLegacy(fct, last) {
			if(!fct.original) return;	//This is the case for non-virtual functions
			while(fct.parent) {
				fct = fct.parent;
				if(fct.terminal) return;
			}
			Object.defineProperty(fct, 'parent', {
				value: last,
				writable: false,
				configurable: false
			});
		}
		function cloneFct(original, name) {
			if(!original) return;
			var Classy = 'constructor'=== name?
				function ClassyConstructorWrapper() { ++constructorCalled[this.oid]; return original.apply(this, arguments); }:
				ext(function ClassyWrapper() { return original.apply(this, arguments); }, {bypass: true});
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
					if('function'=== typeof obj[i] && obj[i].original) {
						if(mFcts) addLegacy(obj[i], oFcts);	//This keeps the virtual chain
						else obj[i] = obj[i].original;	//This indicates it's not a virtual function but a data function (ie. a class specification, ...)
					}	//If obj already has a non-virtual function or a non-functional data, just let it as it is
				} else obj[i] = oFcts;
			}
		}
	}
	ext(Function.prototype, {
		flag: function(obj) { return ext(this, obj); },
		classify: function RegularClassify(obj) { return obj instanceof this; }	// instanceof surrogate - in case of classy is changed to a regular class
	});
	
	classy = ext(function Classy(members) {
		var rv = false, xtnds = [].slice.call(arguments, 1), mFleg=[], orders = {},
			i, j, waitings = {}, ready = '', classes = {}, orgCtor, cname, fname;
			if('function'=== typeof members)
				//if members.prototype.constructor already exists, there is a conflict between 2 constructors - in ExtJs, the function is just a .conctructor.apply
				members = ext({constructor: members}, members.prototype||{});
		//rv -> {cidA: {cidB: true (A before B)} }
		//classes -> {cid: class object}
		function order(rv, classes, list, before, inheriting) {
			var i, j, clss, len;
			function precede(a, b, force) {
				rv[a] || (rv[a] = {});
				rv[b] || (rv[b] = {});
				
				if(force) {
					rv[a][b] = 'f';
					//@ assert No contradictory force : 'f'!== rv[b][a]
					function prune(nb) {
						for(var i in orders[nb]) {
							delete orders[i][a];
							prune(i);
						}
					}
					prune(b);
				} else if(!rv[a][b]) {
					function allowed(nb) {
						for(var i in orders[nb])
							if(orders[i][a] || !allowed(i)) return false;
						return true;
					}
					if(!rv[b][a] && allowed(b)) rv[a][b] = true;
				}
			}
			for(i=0; i<list.length; ++i) {
				if('function'!== typeof (clss = list[i])) throw new classy.exception('Unfitting inheritance : ' + i);
				if(classy!== clss.constructor) {
					if(clss.constructor.classyVersion)
						clss = clss.constructor.classyVersion;
					else clss = clss.constructor.classyVersion = classy(clss);
					list[i] = clss;
				}
				classes[clss.cid] = clss;
				for(j=0; j< inheriting.length; ++j) {
					if(inheriting[j] === clss.cid)
						throw new classy.exception('Cycle in inheritance');	//Impossible
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
		for(i in orders['']) waitings[i] = 0;
		for(i in orders) for(j in orders[i]) ++waitings[j];
		while(false!== ready) {
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
		//@ mode debug
		for(i in waitings)
			//@ assert No class is left waiting in the 'to-extend' queue : !waitings[i]
			;
		//@ endmode

		members || (members = {});
		//@ assert Given members are pure objects : Object.getPrototypeOf(members) === Object.prototype
		if({}.constructor=== members.constructor) members.constructor = (function() {});
		rv = Object.create(rootObject);
		setMbrs(rv, members);
		for(i = 0; i< mFleg.length; ++i)
			setMbrs(rv, mFleg[i].members);
		orgCtor = rv.constructor;
		function ctor() {
			var me=this, ctr = orgCtor;
			
			Object.defineProperty(me, 'oid', {
				value: objectCounter.next(),
				writable: false,
				enumerable: false,
				configurable: false
			});
			
			while(ctr) {
				constructorCalled[me.oid] = 0;
				ctr.apply(me, arguments);
				while(constructorCalled[me.oid]--) ctr = ctr.parent;
			}
			delete constructorCalled[me.oid];
		};
		if(members.constructor.name)
			fname = cname = members.constructor.name;
		else if(members.name) {
			cname = members.name;
			//'_' at the begining to avoid problems with figure-beginned words and reserved keywords
			fname = '_'+cname.replace(/[^\w]/g, '_');
		} else fname = cname = 'ClassyObject';
		rv.constructor = eval('[function '+fname+'() { return ctor.apply(this, arguments); }]')[0];
		//@ mode debug
		for(i in rv)
			if('function'=== typeof rv[i] && (j=rv[i].original) && !j.name && !j.displayName)
				j.displayName = cname+'->'+i;
		//@ endmode
		rv = ext(
			rv.constructor,
			classes = {
				constructor: classy,
				prototype: rv,
				inherits: Object.freeze(xtnds),
				members: Object.freeze(members),
				fleg: Object.freeze(mFleg),
				cid: classCounter.next(),
				classify: function  Classiffy(obj) {
					var me= this, ctr = obj.constructor;
					return me === ctr || (ctr.fleg && 0<= ctr.fleg.indexOf(me));
				},
				extends: function Extends(parent) {
					return 0<= this.fleg.indexOf(parent);
				},
				toString: function ToString() {
					return '[class'+(cname?' '+cname:'')+']';
				},
				name: cname
			}
		);
		for(i in classes) classes[i] = {
			enumerable: false,
			writable: false,
			configurable: false
		};
		Object.defineProperties(rv, classes);
		return rv;
	}, {
		idSpace: idSpace,
		exception: ext(function ClassyException(msg) {
			this.message = msg;
		}, {
			prototype: {
				toString: function() {
					return 'ClassyError: '+this.message;
				}
			}
		}),
		singleton: ext(function ClassySingleton(members) {
			var obj, xtnds = [].slice.call(arguments, 1), classes, mClass, i;
			members || (members = {});
			classes = [members];
			for(i=0; i<xtnds.length; ++i)
				if(!(obj=xtnds[i]) || ('object'!== typeof obj && 'function'!== typeof obj)) throw new classy.exception('Unfitting inheritance : ' + i);
				else classes.push('function'=== typeof xtnds[i]?xtnds[i]:xtnds[i].constructor);
			classes.push(classy.singleton.root || (classy.singleton.root = classy({
				constructor: function Singleton() {},
				toString: function () {
					var cname = this.constructor.name;
					return '[singleton'+(cname?' '+cname:'')+']';
				}
			})));
			mClass = classy.apply(this, classes);
			return new mClass();
		}, {
			extendedMember: function ClassyExtendedMember(me, mbrName) {
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
