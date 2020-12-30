// The code in this file was developed by He-Teng Zhang (National Taiwan University)

#ifndef Glucose_CGlucoseCore_h
#define Glucose_CGlucoseCore_h

/*
 * justification for glucose 
 */

#include "sat/glucose2/Options.h"
#include "sat/glucose2/Solver.h"

ABC_NAMESPACE_IMPL_START

namespace Gluco2 {
inline int  Solver::justUsage() const { return jftr; }

inline Lit  Solver::gateJustFanin(Var v) const {
	assert(v < nVars());
	assert(isJReason(v));


	lbool val0, val1;
	val0 = value(getFaninLit0(v));
	val1 = value(getFaninLit1(v));

	if(isAND(v)){
		// should be handled by conflict analysis before entering here
		assert( value(v) != l_False || l_True  != val0 || l_True  != val1 );

		if(val0 == l_False || val1 == l_False)
			return lit_Undef;

		// branch 
		if(val0 == l_True)
			return ~getFaninLit1(v);
		if(val1 == l_True)
			return ~getFaninLit0(v);

		return maxActiveLit( ~getFaninLit0(v), ~getFaninLit1(v) );
	} else { // xor scope
		// should be handled by conflict analysis before entering here
		assert( value(v) == l_Undef || value(v) != l_False || val0 == val1 );

		// both are assigned
		if( l_Undef != val0 && l_Undef != val1 )
			return lit_Undef;

		// should be handled by propagation before entering here
		assert( l_Undef == val0 && l_Undef == val1 );
		return maxActiveLit( getFaninPlt0(v), getFaninPlt1(v) );
	}
}


// a var should at most be enqueued one time
inline void Solver::pushJustQueue(Var v){
	assert(v < nVars());
	assert(isJReason(v));

	if( ! isRoundWatch(v) )\
		return;


	jdata[v].act_fanin = activity[getFaninVar0(v)] > activity[getFaninVar1(v)]? activity[getFaninVar0(v)]: activity[getFaninVar1(v)];
	jdata[v].now = true;

	jheap.update(v);
}

inline void Solver::ResetJustData(bool fCleanMemory){
	jstack.shrink_( jstack.size() );
	jheap .clear(fCleanMemory);
}

inline Lit Solver::pickJustLit( Var& j_reason ){
	Var next = var_Undef;
	Lit jlit = lit_Undef;

	for( int i = 0; i < jstack.size(); i ++ ){
		Var x = jstack[i];
		if( l_Undef != value(getFaninLit0(x)) || l_Undef != value(getFaninLit1(x)) )
			continue;
		pushJustQueue(x);
	}
	jstack.shrink_( jstack.size() );
	while( ! jheap.empty() && var_Undef != (next = jheap.removeMin()) ){
		if( ! jdata[next].now )
			continue; 

		assert(isJReason(next));
		if( lit_Undef != (jlit = gateJustFanin(next)) )
			break;
		gateAddJwatch(next);
	}

	j_reason = next;
	return jlit;
}


inline void Solver::gateAddJwatch(Var v){
	assert(v < nVars());
	assert(isJReason(v));

	if( var_Undef != jwatch[v].prev ) // already in jwatch
		return;

	assert( var_Undef == jwatch[v].prev );

	lbool val0, val1;
	Var var0, var1;
	var0 = getFaninVar0(v);
	var1 = getFaninVar1(v);
	val0 = value(getFaninLit0(v));
	val1 = value(getFaninLit1(v));

	assert( !isAND(v) ||  l_False == val0 || l_False == val1  );
	assert(  isAND(v) || (l_Undef != val0 && l_Undef != val1) );

	if( (val0 == l_False && val1 == l_False) || !isAND(v) ){
		addJwatch(vardata[var0].level < vardata[var1].level? var0: var1, v);
		return;
	}

	addJwatch(l_False == val0? var0: var1, v);
}

inline void Solver::gateClearJwatch( Var v, int backtrack_level ){
	if( var_Undef == jwatch[v].head )
		return ;

	Var member, next;
	member = jwatch[v].head;
	while( var_Undef != member ){
		next = jwatch[member].next;

		delJwatch( member );

		if( vardata[member].level <= backtrack_level )
			pushJustQueue(member);

		member = next;
	}
}

inline void Solver::updateJustActivity( Var v ){
	for(Lit lfo = var2Fanout0[ v ]; lfo != toLit(~0); lfo = var2FanoutN[ toInt(lfo) ] ){
		Var x = var(lfo);
		if( jdata[x].now && jheap.inHeap(x) ){
			jdata[x].act_fanin = activity[getFaninVar0(x)] > activity[getFaninVar1(x)]? activity[getFaninVar0(x)]: activity[getFaninVar1(x)];
			jheap.update(x);
		}
	}
}


inline void Solver::addJwatch( Var host, Var member ){
	assert( var_Undef == jwatch[member].next && var_Undef == jwatch[member].prev );

	if( var_Undef != jwatch[host].head )
		jwatch[jwatch[host].head].prev = member;

	jwatch[member].next = jwatch[host].head;
	jwatch[member].prev = host;
	jwatch[host].head = member;
}

inline void Solver::delJwatch( Var member ){
	Var prev = jwatch[member].prev;
	Var next = jwatch[member].next;

	assert( var_Undef != prev ); // must be in a list to be deleted 
	assert( jwatch[prev].next == member || jwatch[prev].head == member );

	if( jwatch[prev].next == member )
		jwatch[prev].next = next;
	else 
		jwatch[prev].head = next;

	if( var_Undef != next )
		jwatch[next].prev = prev;

	jwatch[member].prev = var_Undef;
	jwatch[member].next = var_Undef;
}


/*
 * circuit propagation 
 */

inline void Solver::justCheck(){
	Lit lit;
	int i, nJustFail = 0;
	for(i=0; i<trail.size(); i++){
		Var      x  = var(trail[i]);
		if( ! isRoundWatch(x) )
			continue;
		if( !isJReason(x) )
			continue;
		if( lit_Undef != (lit = gateJustFanin(x)) ){
			printf("\t%8d is not justified (value=%d, level=%3d)\n", x, l_True == value(x)? 1: 0, vardata[x].level), nJustFail ++ ;

			assert(false);
		}
	}
	if( nJustFail )
		printf("%d just-fails\n", nJustFail);
}
/**
inline void Solver::delVarFaninLits( Var v ){
	if( toLit(~0) != getFaninLit0(v) ){
		if( toLit(~0) == var2FanoutP[ (v<<1) + 0 ] ){
			// head of linked-list 
			Lit root = mkLit(getFaninVar0(v));
			Lit next = var2FanoutN[ (v<<1) + 0 ];
			if( toLit(~0) != next ){
				assert( var2Fanout0[ toInt(root) ] == toLit((v<<1) + 0) );
				assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 0) );
				var2Fanout0[ getFaninVar0(v) ] = next;
				var2FanoutP[ toInt(next) ] = toLit(~0);
			}
		} else {
			Lit prev = var2FanoutP[ (v<<1) + 0 ];
			Lit next = var2FanoutN[ (v<<1) + 0 ];
			if( toLit(~0) != next ){
				assert( var2FanoutN[ toInt(prev) ] == toLit((v<<1) + 0) );
				assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 0) );
				var2FanoutN[ toInt(prev) ] = next;
				var2FanoutP[ toInt(next) ] = prev;
			}
		}
	}


	if( toLit(~0) != getFaninLit1(v) ){
		if( toLit(~0) == var2FanoutP[ (v<<1) + 1 ] ){
			// head of linked-list 
			Lit root = mkLit(getFaninVar1(v));
			Lit next = var2FanoutN[ (v<<1) + 1 ];
			if( toLit(~0) != next ){
				assert( var2Fanout0[ toInt(root) ] == toLit((v<<1) + 1) );
				assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 1) );
				var2Fanout0[ getFaninVar1(v) ] = next;
				var2FanoutP[ toInt(next) ] = toLit(~0);
			}
		} else {
			Lit prev = var2FanoutP[ (v<<1) + 1 ];
			Lit next = var2FanoutN[ (v<<1) + 1 ];
			if( toLit(~0) != next ){
				assert( var2FanoutN[ toInt(prev) ] == toLit((v<<1) + 1) );
				assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 1) );
				var2FanoutN[ toInt(prev) ] = next;
				var2FanoutP[ toInt(next) ] = prev;
			}
		}
	}

	var2FanoutP  [ (v<<1) + 0 ] = toLit(~0);
	var2FanoutP  [ (v<<1) + 1 ] = toLit(~0);
	var2FanoutN  [ (v<<1) + 0 ] = toLit(~0);
	var2FanoutN  [ (v<<1) + 1 ] = toLit(~0);
	var2FaninLits[ (v<<1) + 0 ] = toLit(~0);
	var2FaninLits[ (v<<1) + 1 ] = toLit(~0);
}
**/
inline void Solver::setVarFaninLits( Var v, Lit lit1, Lit lit2 ){
	assert( var(lit1) != var(lit2) );
	int mincap = var(lit1) < var(lit2)? var(lit2): var(lit1);
	mincap = (v < mincap? mincap: v) + 1;

	if( var2FaninLits.size() < (mincap<<1) )
		var2FaninLits.growTo( (mincap<<1), toLit(~0));
	assert( (toLit(~0) == lit1 && toLit(~0) == lit2) || ((v<<1)+1 < var2FaninLits.size()) );
	var2FaninLits[ (v<<1) + 0 ] = lit1;
	var2FaninLits[ (v<<1) + 1 ] = lit2;


	assert( toLit(~0) != lit1 && toLit(~0) != lit2 );


	if( var2FanoutN.size() < (mincap<<1) )
		var2FanoutN.growTo( (mincap<<1), toLit(~0));
	//if( var2FanoutP.size() < (mincap<<1) )
	//	var2FanoutP.growTo( (mincap<<1), toLit(~0));
	if( var2Fanout0.size() < mincap )
		var2Fanout0.growTo( mincap, toLit(~0));

	var2FanoutN[ (v<<1) + 0 ] = var2Fanout0[ var(lit1) ];
	var2FanoutN[ (v<<1) + 1 ] = var2Fanout0[ var(lit2) ];
	var2Fanout0[ var(lit1) ] = toLit( (v<<1) + 0 );
	var2Fanout0[ var(lit2) ] = toLit( (v<<1) + 1 );

	//if( toLit(~0) != var2FanoutN[ (v<<1) + 0 ] )
	//	var2FanoutP[ toInt(var2FanoutN[ (v<<1) + 0 ]) ] = toLit((v<<1) + 0);

	//if( toLit(~0) != var2FanoutN[ (v<<1) + 1 ] )
	//	var2FanoutP[ toInt(var2FanoutN[ (v<<1) + 1 ]) ] = toLit((v<<1) + 1);
}


inline bool Solver::isTwoFanin( Var v ) const {
	assert(v < nVars());
	if( var2FaninLits.size() <= (v<<1)+1 )
		return false;
	Lit lit0 = var2FaninLits[ (v<<1) + 0 ];
	Lit lit1 = var2FaninLits[ (v<<1) + 1 ];
	assert( toLit(~0) == lit0 || var(lit0) < nVars() );
	assert( toLit(~0) == lit1 || var(lit1) < nVars() );
    lit0.x = lit1.x = 0; // suppress the warning - alanmi
	return toLit(~0) != var2FaninLits[ (v<<1) + 0 ] && toLit(~0) != var2FaninLits[ (v<<1) + 1 ];
}

// this implementation return the last conflict encountered
// which follows minisat concept
inline CRef Solver::gatePropagate( Lit p ){
	CRef confl = CRef_Undef, stats;
	if( justUsage() < 2 || var2FaninLits.size() <= var(p) )
		return CRef_Undef;

	if( ! isRoundWatch(var(p)) )
		return CRef_Undef;

	if( ! isTwoFanin( var(p) ) )
		goto check_fanout;


	// check fanin consistency 
	if( CRef_Undef != (stats = gatePropagateCheckThis( var(p) )) ){
		confl = stats;
		if( l_True == value(var(p)) )
			return confl;
	}

	// check fanout consistency
check_fanout:
	assert( var(p) < var2Fanout0.size() );

	for( Lit lfo = var2Fanout0[ var(p) ]; lfo != toLit(~0); lfo = var2FanoutN[ toInt(lfo) ] )
	{
		if( ! isRoundWatch(var(lfo)) ) continue;

		if( CRef_Undef != (stats = gatePropagateCheckFanout( var(p), lfo )) ){
			confl = stats;
			if( l_True == value(var(lfo)) )
				return confl;
		}
	}

	return confl;
}

inline CRef Solver::gatePropagateCheckFanout( Var v, Lit lfo ){
	Lit faninLit = sign(lfo)? getFaninLit1(var(lfo)): getFaninLit0(var(lfo));
	assert( var(faninLit) == v );
	if( isAND(var(lfo)) ){
		if( l_False == value(faninLit) )
		{
			if( l_False == value(var(lfo)) )
				return CRef_Undef;

			if( l_True == value(var(lfo)) )
				return Var2CRef(var(lfo));
			
			jwatch[var(lfo)].header.dir = sign(lfo);
			uncheckedEnqueue(~mkLit(var(lfo)), Var2CRef( var(lfo) ) );
		} else {
			assert( l_True == value(faninLit) );

			if( l_True == value(var(lfo)) )
				return CRef_Undef;
			
			// check value of the other fanin 
			Lit faninLitP = sign(lfo)? getFaninLit0(var(lfo)): getFaninLit1(var(lfo));
			if( l_False == value(var(lfo)) ){
				
				if( l_False == value(faninLitP) )
					return CRef_Undef;

				if( l_True == value(faninLitP) )
					return Var2CRef(var(lfo));

				uncheckedEnqueue( ~faninLitP, Var2CRef( var(lfo) ) );
			}
			else
			if( l_True == value(faninLitP) )
				uncheckedEnqueue( mkLit(var(lfo)), Var2CRef( var(lfo) ) );
		}
	} else { // xor scope
		// check value of the other fanin 
		Lit faninLitP = sign(lfo)? getFaninLit0(var(lfo)): getFaninLit1(var(lfo));

		lbool val0, val1, valo;
		val0 = value(faninLit );
		val1 = value(faninLitP);
		valo = value(var(lfo));

		if( l_Undef == val1 && l_Undef == valo )
			return CRef_Undef;
		else
		if( l_Undef == val1 )
			uncheckedEnqueue( ~faninLitP ^ ( (l_True == val0) ^ (l_True == valo) ), Var2CRef( var(lfo) ) );
		else
		if( l_Undef == valo )
			uncheckedEnqueue( ~mkLit( var(lfo), (l_True == val0) ^ (l_True == val1) ), Var2CRef( var(lfo) ) );
		else
		if( l_False  == (valo ^ (val0 == val1)) )
			return Var2CRef(var(lfo));

	}
	
	return CRef_Undef;
}

inline CRef Solver::gatePropagateCheckThis( Var v ){
	CRef confl = CRef_Undef;
	if( isAND(v) ){
		if( l_False == value(v) ){
			if( l_True == value(getFaninLit0(v)) && l_True == value(getFaninLit1(v)) )
				return Var2CRef(v);

			if( l_False == value(getFaninLit0(v)) || l_False == value(getFaninLit1(v)) )
				return CRef_Undef;

			if( l_True == value(getFaninLit0(v)) )
				uncheckedEnqueue(~getFaninLit1( v ), Var2CRef( v ) );
			if( l_True == value(getFaninLit1(v)) )
				uncheckedEnqueue(~getFaninLit0( v ), Var2CRef( v ) );
		} else {
			assert( l_True == value(v) );
			if( l_False == value(getFaninLit0(v)) || l_False == value(getFaninLit1(v)) )
				confl = Var2CRef(v);

			if( l_Undef == value( getFaninLit0( v )) )
				uncheckedEnqueue( getFaninLit0( v ), Var2CRef( v ) );

			if( l_Undef == value( getFaninLit1( v )) )
				uncheckedEnqueue( getFaninLit1( v ), Var2CRef( v ) );

		}
	} else { // xor scope
		lbool val0, val1, valo;
		val0 = value(getFaninLit0(v));
		val1 = value(getFaninLit1(v));
		valo = value(v);
		if( l_Undef == val0 && l_Undef == val1 )
			return CRef_Undef;
		if( l_Undef == val0 )
			uncheckedEnqueue(~getFaninLit0( v ) ^ ( (l_True == val1) ^ (l_True == valo) ), Var2CRef( v ) );
		else
		if( l_Undef == val1 )
			uncheckedEnqueue(~getFaninLit1( v ) ^ ( (l_True == val0) ^ (l_True == valo) ), Var2CRef( v ) );
		else
		if( l_False == (valo ^ (val0 == val1)) )
			return Var2CRef(v);
	}

	return confl;
}

inline CRef Solver::getConfClause( CRef r ){
	if( !isGateCRef(r) )
		return r;
	Var v = CRef2Var(r);
	assert( isTwoFanin(v) );

	if(isAND(v)){
		if( l_False == value(v) ){
			setItpcSize(3);
			Clause& c = ca[itpc];
			c[0] = mkLit(v);
			c[1] = ~getFaninLit0( v );
			c[2] = ~getFaninLit1( v );
		} else {
			setItpcSize(2);
			Clause& c = ca[itpc];
			c[0] = ~mkLit(v);

			lbool val0 = value(getFaninLit0(v));
			lbool val1 = value(getFaninLit1(v));

			if( l_False == val0 && l_False == val1 )
				c[1] = level(getFaninVar0(v)) < level(getFaninVar1(v))? getFaninLit0( v ): getFaninLit1( v );
			else
			if( l_False == val0 )
				c[1] = getFaninLit0( v );
			else
				c[1] = getFaninLit1( v );
		}
	} else { // xor scope
		setItpcSize(3);
		Clause& c = ca[itpc];
		c[0] = mkLit(v, l_True == value(v));
		c[1] = mkLit(getFaninVar0(v), l_True == value(getFaninVar0(v)));
		c[2] = mkLit(getFaninVar1(v), l_True == value(getFaninVar1(v)));
	}
	

	return itpc;
}

inline void Solver::setItpcSize( int sz ){
	assert( 3 >= sz );
	assert( CRef_Undef != itpc );
	ca[itpc].header.size = sz;
}

inline CRef Solver::interpret( Var v, Var t )
{ // get gate-clause on implication graph
	assert( isTwoFanin(v) );

	lbool val0, val1, valo;
	Var var0, var1;
	var0 = getFaninVar0( v );
	var1 = getFaninVar1( v );
	val0 = value(var0);
	val1 = value(var1);
	valo = value( v );

	// phased values
	if(l_Undef != val0) val0 = val0 ^ getFaninC0( v );
	if(l_Undef != val1) val1 = val1 ^ getFaninC1( v );


	if( isAND(v) ){
		if( v == t ){ // tracing output 
			if( l_False == valo ){
				setItpcSize(2);
				Clause& c = ca[itpc];
				c[0] = ~mkLit(v);

				if( l_False == val0 && l_False == val1 )
					c[1] = 0 == jwatch[v].header.dir ? getFaninLit0( v ): getFaninLit1( v );
				else
				if( l_False == val0 )
					c[1] = getFaninLit0( v );
				else
					c[1] = getFaninLit1( v );
			} else {
				setItpcSize(3);
				Clause& c = ca[itpc];
				c[0] = mkLit(v);
				c[1] = ~getFaninLit0( v );
				c[2] = ~getFaninLit1( v );
			}
		} else {
			assert( t == var0 || t == var1 );
			if( l_False == valo ){
				setItpcSize(3);
				Clause& c = ca[itpc];
				c[0] = ~getFaninLit0( v );
				c[1] = ~getFaninLit1( v );
				c[2] = mkLit(v);
				if( t == var1 )
	                c[1].x ^= c[0].x, c[0].x ^= c[1].x, c[1].x ^= c[0].x;
			} else {
				setItpcSize(2);
				Clause& c = ca[itpc];
				c[0] =  t == var0? getFaninLit0( v ): getFaninLit1( v );
				c[1] = ~mkLit(v);
			}
		}
	} else { // xor scope
		setItpcSize(3);
		Clause& c = ca[itpc];
		if( v == t ){
			c[0] = mkLit(v, l_False == value(v));
			c[1] = mkLit(var0, l_True == value(var0));
			c[2] = mkLit(var1, l_True == value(var1));
		} else {
			if( t == var0)
				c[0] = mkLit(var0, l_False == value(var0)), c[1] = mkLit(var1, l_True  == value(var1));
			else
				c[1] = mkLit(var0, l_True  == value(var0)), c[0] = mkLit(var1, l_False == value(var1));
			c[2] = mkLit(v, l_True == value(v));
		}
	}

	return itpc;
}

inline CRef Solver::castCRef( Lit p ){
	CRef cr = reason( var(p) );
	if( CRef_Undef == cr )
		return cr;
	if( ! isGateCRef(cr) )
		return cr;
	Var v = CRef2Var(cr);
	return interpret(v,var(p));
}

inline void Solver::markCone( Var v ){
	if( var2TravId[v] >= travId )
		return;
	var2TravId[v] = travId;

	if( !isTwoFanin(v) )
		return;
	markCone( getFaninVar0(v) );
	markCone( getFaninVar1(v) );
}

};

ABC_NAMESPACE_IMPL_END

#endif
