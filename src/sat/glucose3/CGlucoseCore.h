// The code in this file was developed by He-Teng Zhang (National Taiwan University)

#ifndef Glucose3_CGlucoseCore_h
#define Glucose3_CGlucoseCore_h

//
// justification for glucose
//

#include "sat/glucose3/Options.h"
#include "sat/glucose3/Solver.h"

ABC_NAMESPACE_IMPL_START

namespace Gluco3 {
inline int  Solver::justUsage() const { return jftr; }

inline Lit  Solver::gateJustFanin(Var v) const {
	assert(v < nVars());
	assert(isJReason(v));


	lbool val0, val1;
	val0 = value(getFaninLit0(v));
	val1 = value(getFaninLit1(v));

	if(isAND(v)){
		// should be handled by conflict analysis before entering here
		assert( value(v) != G3_l_False || G3_l_True  != val0 || G3_l_True  != val1 );

		if(val0 == G3_l_False || val1 == G3_l_False)
			return lit_Undef;

		// branch
		if(val0 == G3_l_True)
			return ~getFaninLit1(v);
		if(val1 == G3_l_True)
			return ~getFaninLit0(v);

		//assert( jdata[v].act_fanin == activity[getFaninVar0(v)] || jdata[v].act_fanin == activity[getFaninVar1(v)] );
		//assert( jdata[v].act_fanin == (jdata[v].adir? activity[getFaninVar1(v)]: activity[getFaninVar0(v)]) );
		return maxActiveLit( ~getFaninLit0(v), ~getFaninLit1(v) );
		//return jdata[v].adir? ~getFaninLit1(v): ~getFaninLit0(v);
	} else { // xor scope
		// should be handled by conflict analysis before entering here
		assert( value(v) == G3_l_Undef || value(v) != G3_l_False || val0 == val1 );

		// both are assigned
		if( G3_l_Undef != val0 && G3_l_Undef != val1 )
			return lit_Undef;

		// should be handled by propagation before entering here
		assert( G3_l_Undef == val0 && G3_l_Undef == val1 );
		return maxActiveLit( getFaninPlt0(v), getFaninPlt1(v) );
	}
}


// a var should at most be enqueued one time
inline void Solver::pushJustQueue(Var v, int index){
	assert(v < nVars());
	assert(isJReason(v));

	if( ! isRoundWatch(v) )\
		return;

	var2NodeData[v].now = true;


	if( activity[getFaninVar1(v)] > activity[getFaninVar0(v)] )
		jheap.update( JustKey( activity[getFaninVar1(v)], v, index ) );
	else
		jheap.update( JustKey( activity[getFaninVar0(v)], v, index ) );
}

inline void Solver::uncheckedEnqueue2(Lit p, CRef from)
{
    //assert( isRoundWatch(var(p)) ); // inplace sorting guarantee this
    assert(value(p) == G3_l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}

inline void Solver::ResetJustData(bool fCleanMemory){
	jhead = 0;
	jheap .clear_( fCleanMemory );
}

inline Lit Solver::pickJustLit( int& index ){
	Var next = G3_var_Undef;
	Lit jlit = lit_Undef;

	for( ; jhead < trail.size() ; jhead++ ){
		Var x = var(trail[jhead]);
		if( !decisionLevel() && !isRoundWatch(x) ) continue;
		if( isJReason(x) && G3_l_Undef == value( getFaninVar0(x) ) && G3_l_Undef == value( getFaninVar1(x) ) )
			pushJustQueue(x,jhead);
	}

	while( ! jheap.empty() ){
		next = jheap.removeMin(index);
		if( ! var2NodeData[next].now )
			continue;

		assert(isJReason(next));
		if( lit_Undef != (jlit = gateJustFanin(next)) ){
			//assert( jheap.prev.key() == activity[getFaninVar0(next)] || jheap.prev.key() == activity[getFaninVar1(next)] );
			break;
		}
		gateAddJwatch(next,index);
	}

	return jlit;
}


inline void Solver::gateAddJwatch(Var v,int index){
	assert(v < nVars());
	assert(isJReason(v));

	lbool val0, val1;
	Var var0, var1;
	var0 = getFaninVar0(v);
	var1 = getFaninVar1(v);
	val0 = value(getFaninLit0(v));
	val1 = value(getFaninLit1(v));

	assert( !isAND(v) ||  G3_l_False == val0 || G3_l_False == val1  );
	assert(  isAND(v) || (G3_l_Undef != val0 && G3_l_Undef != val1) );

	if( (val0 == G3_l_False && val1 == G3_l_False) || !isAND(v) ){
		addJwatch(vardata[var0].level < vardata[var1].level? var0: var1, v, index);
		return;
	}

	addJwatch(G3_l_False == val0? var0: var1, v, index);

	return;
}

inline void Solver::updateJustActivity( Var v ){
    if ( useConeFanouts )
    {
        for ( int edge = coneFanoutHeads[v]; edge >= 0; edge = coneFanoutNext[edge] )
        {
            Var x = edge >> 1;
            if ( var2NodeData[x].now && jheap.inHeap(x) )
            {
                double a = activity[getFaninVar0(x)], b = activity[getFaninVar1(x)];
                jheap.update( JustKey(a > b ? a : b, x, jheap.data_attr(x)) );
            }
        }
        return;
    }
	if( ! var2NodeData[v].sort )
		inplace_sort(v);

	int nFanout = 0;
	for(Lit lfo = var2Fanout0[ v ]; nFanout < var2NodeData[v].sort; lfo = var2FanoutN[ toInt(lfo) ], nFanout ++ ){
		Var x = var(lfo);
		if( var2NodeData[x].now && jheap.inHeap(x) ){
			if( activity[getFaninVar1(x)] > activity[getFaninVar0(x)] )
				jheap.update( JustKey( activity[getFaninVar1(x)], x, jheap.data_attr(x) ) );
			else
				jheap.update( JustKey( activity[getFaninVar0(x)], x, jheap.data_attr(x) ) );
		}
	}
}


inline void Solver::addJwatch( Var host, Var member, int index ){
	assert(level(host) >= level(member));
	jnext[index] = jlevel[level(host)];
	jlevel[level(host)] = index;
}

//
// circuit propagation
//

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
			printf("\t%8d is not justified (value=%d, level=%3d)\n", x, G3_l_True == value(x)? 1: 0, vardata[x].level), nJustFail ++ ;

			assert(false);
		}
	}
	if( nJustFail )
		printf("%d just-fails\n", nJustFail);
}
// *
// inline void Solver::delVarFaninLits( Var v ){
// if( toLit(~0) != getFaninLit0(v) ){
// if( toLit(~0) == var2FanoutP[ (v<<1) + 0 ] ){
// // head of linked-list
// Lit root = mkLit(getFaninVar0(v));
// Lit next = var2FanoutN[ (v<<1) + 0 ];
// if( toLit(~0) != next ){
// assert( var2Fanout0[ toInt(root) ] == toLit((v<<1) + 0) );
// assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 0) );
// var2Fanout0[ getFaninVar0(v) ] = next;
// var2FanoutP[ toInt(next) ] = toLit(~0);
// }
// } else {
// Lit prev = var2FanoutP[ (v<<1) + 0 ];
// Lit next = var2FanoutN[ (v<<1) + 0 ];
// if( toLit(~0) != next ){
// assert( var2FanoutN[ toInt(prev) ] == toLit((v<<1) + 0) );
// assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 0) );
// var2FanoutN[ toInt(prev) ] = next;
// var2FanoutP[ toInt(next) ] = prev;
// }
// }
// }
//
//
// if( toLit(~0) != getFaninLit1(v) ){
// if( toLit(~0) == var2FanoutP[ (v<<1) + 1 ] ){
// // head of linked-list
// Lit root = mkLit(getFaninVar1(v));
// Lit next = var2FanoutN[ (v<<1) + 1 ];
// if( toLit(~0) != next ){
// assert( var2Fanout0[ toInt(root) ] == toLit((v<<1) + 1) );
// assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 1) );
// var2Fanout0[ getFaninVar1(v) ] = next;
// var2FanoutP[ toInt(next) ] = toLit(~0);
// }
// } else {
// Lit prev = var2FanoutP[ (v<<1) + 1 ];
// Lit next = var2FanoutN[ (v<<1) + 1 ];
// if( toLit(~0) != next ){
// assert( var2FanoutN[ toInt(prev) ] == toLit((v<<1) + 1) );
// assert( var2FanoutP[ toInt(next) ] == toLit((v<<1) + 1) );
// var2FanoutN[ toInt(prev) ] = next;
// var2FanoutP[ toInt(next) ] = prev;
// }
// }
// }
//
// var2FanoutP  [ (v<<1) + 0 ] = toLit(~0);
// var2FanoutP  [ (v<<1) + 1 ] = toLit(~0);
// var2FanoutN  [ (v<<1) + 0 ] = toLit(~0);
// var2FanoutN  [ (v<<1) + 1 ] = toLit(~0);
// var2FaninLits[ (v<<1) + 0 ] = toLit(~0);
// var2FaninLits[ (v<<1) + 1 ] = toLit(~0);
// }
// *
inline void Solver::setVarFaninLits( Var v, Lit lit1, Lit lit2 ){
	assert( var(lit1) != var(lit2) );
	int mincap = var(lit1) < var(lit2)? var(lit2): var(lit1);
	mincap = (v < mincap? mincap: v) + 1;

	var2NodeData[ v ].lit0 = lit1;
	var2NodeData[ v ].lit1 = lit2;


	assert( toLit(~0) != lit1 && toLit(~0) != lit2 );

	var2FanoutN[ (v<<1) + 0 ] = var2Fanout0[ var(lit1) ];
	var2FanoutN[ (v<<1) + 1 ] = var2Fanout0[ var(lit2) ];
	var2Fanout0[ var(lit1) ] = toLit( (v<<1) + 0 );
	var2Fanout0[ var(lit2) ] = toLit( (v<<1) + 1 );
    // Inserting even an inactive fanout changes the sorted active prefix.
    var2NodeData[var(lit1)].sort = 0;
    var2NodeData[var(lit2)].sort = 0;

	//if( toLit(~0) != var2FanoutN[ (v<<1) + 0 ] )
	//	var2FanoutP[ toInt(var2FanoutN[ (v<<1) + 0 ]) ] = toLit((v<<1) + 0);

	//if( toLit(~0) != var2FanoutN[ (v<<1) + 1 ] )
	//	var2FanoutP[ toInt(var2FanoutN[ (v<<1) + 1 ]) ] = toLit((v<<1) + 1);
}


inline bool Solver::isTwoFanin( Var v ) const {
	Lit lit0 = var2NodeData[ v ].lit0;
	Lit lit1 = var2NodeData[ v ].lit1;
	assert( toLit(~0) == lit0 || var(lit0) < nVars() );
	assert( toLit(~0) == lit1 || var(lit1) < nVars() );
    lit0.x = lit1.x = 0; // suppress the warning - alanmi
	return toLit(~0) != var2NodeData[ v ].lit0 && toLit(~0) != var2NodeData[ v ].lit1;
}

// this implementation return the last conflict encountered
// which follows minisat concept
inline CRef Solver::gatePropagate( Lit p ){
	CRef confl = CRef_Undef, stats;
	if( justUsage() < 2 )
		return CRef_Undef;

	if( ! isRoundWatch(var(p)) )
		return CRef_Undef;

	if( ! isTwoFanin( var(p) ) )
		goto check_fanout;


	// check fanin consistency
	if( CRef_Undef != (stats = gatePropagateCheckThis( var(p) )) ){
		confl = stats;
		if( G3_l_True == value(var(p)) )
			return confl;
	}

	// check fanout consistency
check_fanout:
	assert( var(p) < var2Fanout0.size() );

    if ( useConeFanouts )
    {
        for ( int edge = coneFanoutHeads[var(p)]; edge >= 0; edge = coneFanoutNext[edge] )
            if ( CRef_Undef != (stats = gatePropagateCheckFanout(var(p), toLit(edge))) )
            {
                confl = stats;
                if ( G3_l_True == value(edge >> 1) ) return confl;
            }
        return confl;
    }

	if( ! var2NodeData[var(p)].sort )
		inplace_sort(var(p));

	int nFanout = 0;
	for( Lit lfo = var2Fanout0[ var(p) ]; nFanout < var2NodeData[var(p)].sort; lfo = var2FanoutN[ toInt(lfo) ], nFanout ++ )
	{
		if( CRef_Undef != (stats = gatePropagateCheckFanout( var(p), lfo )) ){
			confl = stats;
			if( G3_l_True == value(var(lfo)) )
				return confl;
		}
	}

	return confl;
}

// Read each gate state once. Values 0/1 mean true/false; either 2 or 3
// means unassigned after applying an input literal's complement bit.
// Keep the original enqueue and conflict order exactly.
inline CRef Solver::gatePropagateCheckFanout( Var v, Lit lfo )
{
    const Var out = var(lfo);
    const NodeData& gate = var2NodeData[out];
    const Lit input = sign(lfo) ? gate.lit1 : gate.lit0;
    const int inValue = toInt(assigns[v]) ^ sign(input);
    const int outValue = toInt(assigns[out]);
    assert( var(input) == v && inValue < 2 );
    if ( toInt(gate.lit0) < toInt(gate.lit1) )
    {
        if ( inValue == 1 )
        {
            if ( outValue == 1 ) return CRef_Undef;
            if ( outValue == 0 ) return Var2CRef(out);
            var2NodeData[out].dir = sign(lfo);
            uncheckedEnqueue2(~mkLit(out), Var2CRef(out));
        }
        else
        {
            if ( outValue == 0 ) return CRef_Undef;
            const Lit other = sign(lfo) ? gate.lit0 : gate.lit1;
            const int otherValue = toInt(assigns[var(other)]) ^ sign(other);
            if ( outValue == 1 )
            {
                if ( otherValue == 1 ) return CRef_Undef;
                if ( otherValue == 0 ) return Var2CRef(out);
                uncheckedEnqueue2(~other, Var2CRef(out));
            }
            else if ( otherValue == 0 )
                uncheckedEnqueue2(mkLit(out), Var2CRef(out));
        }
    }
    else
    {
        const Lit other = sign(lfo) ? gate.lit0 : gate.lit1;
        const int otherValue = toInt(assigns[var(other)]) ^ sign(other);
        if ( otherValue >= 2 && outValue >= 2 ) return CRef_Undef;
        if ( otherValue >= 2 )
            uncheckedEnqueue2(~other ^ ((inValue == 0) ^ (outValue == 0)), Var2CRef(out));
        else if ( outValue >= 2 )
            uncheckedEnqueue2(~mkLit(out, (inValue == 0) ^ (otherValue == 0)), Var2CRef(out));
        else if ( (outValue ^ (inValue == otherValue)) == 1 )
            return Var2CRef(out);
    }
    return CRef_Undef;
}

inline CRef Solver::gatePropagateCheckThis( Var v )
{
    const NodeData& gate = var2NodeData[v];
    const Lit input0 = gate.lit0, input1 = gate.lit1;
    const int value0 = toInt(assigns[var(input0)]) ^ sign(input0);
    const int value1 = toInt(assigns[var(input1)]) ^ sign(input1);
    const int outValue = toInt(assigns[v]);
    CRef conflict = CRef_Undef;
    if ( toInt(input0) < toInt(input1) )
    {
        if ( outValue == 1 )
        {
            if ( value0 == 0 && value1 == 0 ) return Var2CRef(v);
            if ( value0 == 1 || value1 == 1 ) return CRef_Undef;
            if ( value0 == 0 ) uncheckedEnqueue2(~input1, Var2CRef(v));
            if ( value1 == 0 ) uncheckedEnqueue2(~input0, Var2CRef(v));
        }
        else
        {
            assert( outValue == 0 );
            if ( value0 == 1 || value1 == 1 ) conflict = Var2CRef(v);
            if ( value0 >= 2 ) uncheckedEnqueue2(input0, Var2CRef(v));
            if ( value1 >= 2 ) uncheckedEnqueue2(input1, Var2CRef(v));
        }
    }
    else
    {
        if ( value0 >= 2 && value1 >= 2 ) return CRef_Undef;
        if ( value0 >= 2 )
            uncheckedEnqueue2(~input0 ^ ((value1 == 0) ^ (outValue == 0)), Var2CRef(v));
        else if ( value1 >= 2 )
            uncheckedEnqueue2(~input1 ^ ((value0 == 0) ^ (outValue == 0)), Var2CRef(v));
        else if ( (outValue ^ (value0 == value1)) == 1 )
            return Var2CRef(v);
    }
    return conflict;
}

inline CRef Solver::getConfClause( CRef r ){
	if( !isGateCRef(r) )
		return r;
	Var v = CRef2Var(r);
	assert( isTwoFanin(v) );

	if(isAND(v)){
		if( G3_l_False == value(v) ){
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

			if( G3_l_False == val0 && G3_l_False == val1 )
				c[1] = level(getFaninVar0(v)) < level(getFaninVar1(v))? getFaninLit0( v ): getFaninLit1( v );
			else
			if( G3_l_False == val0 )
				c[1] = getFaninLit0( v );
			else
				c[1] = getFaninLit1( v );
		}
	} else { // xor scope
		setItpcSize(3);
		Clause& c = ca[itpc];
		c[0] = mkLit(v, G3_l_True == value(v));
		c[1] = mkLit(getFaninVar0(v), G3_l_True == value(getFaninVar0(v)));
		c[2] = mkLit(getFaninVar1(v), G3_l_True == value(getFaninVar1(v)));
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
	if(G3_l_Undef != val0) val0 = val0 ^ getFaninC0( v );
	if(G3_l_Undef != val1) val1 = val1 ^ getFaninC1( v );


	if( isAND(v) ){
		if( v == t ){ // tracing output
			if( G3_l_False == valo ){
				setItpcSize(2);
				Clause& c = ca[itpc];
				c[0] = ~mkLit(v);

				c[1] = var2NodeData[v].dir ? getFaninLit1( v ): getFaninLit0( v );
			} else {
				setItpcSize(3);
				Clause& c = ca[itpc];
				c[0] = mkLit(v);
				c[1] = ~getFaninLit0( v );
				c[2] = ~getFaninLit1( v );
			}
		} else {
			assert( t == var0 || t == var1 );
			if( G3_l_False == valo ){
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
			c[0] = mkLit(v, G3_l_False == value(v));
			c[1] = mkLit(var0, G3_l_True == value(var0));
			c[2] = mkLit(var1, G3_l_True == value(var1));
		} else {
			if( t == var0)
				c[0] = mkLit(var0, G3_l_False == value(var0)), c[1] = mkLit(var1, G3_l_True  == value(var1));
			else
				c[1] = mkLit(var0, G3_l_True  == value(var0)), c[0] = mkLit(var1, G3_l_False == value(var1));
			c[2] = mkLit(v, G3_l_True == value(v));
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

// References count selected roots and edges from active gates. Only a change
// between zero and nonzero membership requires visiting the node's fanins.
inline void Solver::coneRef( Var v, int delta )
{
    int old = coneRefs[v];
    coneRefs[v] += delta;
    assert( coneRefs[v] >= 0 );
    if ( delta > 0 ? old != 0 : coneRefs[v] != 0 )
        return;
    var2TravId[v] = delta > 0 ? 1 : 0;
    var2NodeData[v].sort = 0;
    if ( !isTwoFanin(v) )
        return;
    Var a = getFaninVar0(v), b = getFaninVar1(v);
    // The multi-root interface maintains precisely the active edges.
    // No scan of old query gates or unselected side cones is needed during
    // propagation. The original two-root interface keeps its old ordering.
    if ( useConeFanouts )
        for ( int k = 0; k < 2; k++ )
        {
            int edge = 2*v + k, fanin = k ? b : a;
            if ( delta > 0 )
            {
                int head = coneFanoutHeads[fanin];
                coneFanoutPrev[edge] = -1;
                coneFanoutNext[edge] = head;
                if ( head >= 0 ) coneFanoutPrev[head] = edge;
                coneFanoutHeads[fanin] = edge;
            }
            else
            {
                int prev = coneFanoutPrev[edge], next = coneFanoutNext[edge];
                if ( prev < 0 ) coneFanoutHeads[fanin] = next;
                else coneFanoutNext[prev] = next;
                if ( next >= 0 ) coneFanoutPrev[next] = prev;
                coneFanoutPrev[edge] = coneFanoutNext[edge] = -1;
            }
        }
    var2NodeData[a].sort = 0;
    var2NodeData[b].sort = 0;
    coneRef( a, delta );
    coneRef( b, delta );
}

inline void Solver::selectCone( Var v0, Var v1 )
{
    assert( !useConeFanouts );
    if ( coneRoot0 == -2 )
    {
        for ( int i = 0; i < var2TravId.size(); i++ )
            var2TravId[i] = 0;
        travId = 1;
        coneRoot0 = coneRoot1 = -1;
    }
    assert( travId == 1 );
    coneRefs.growTo( nVars(), 0 );
    // Add first: shared fanin nodes keep their references and need no traversal.
    if ( v0 >= 0 ) coneRef( v0, 1 );
    if ( v1 >= 0 ) coneRef( v1, 1 );
    if ( coneRoot0 >= 0 ) coneRef( coneRoot0, -1 );
    if ( coneRoot1 >= 0 ) coneRef( coneRoot1, -1 );
    coneRoot0 = v0;
    coneRoot1 = v1;
}

// Multiple required roots use the same exact cone references as two-root
// sweeping. A solver instance uses one of these interfaces until its reset.
inline void Solver::selectCones( const int * roots, int count )
{
    if ( coneRoot0 == -2 )
    {
        for ( int i = 0; i < var2TravId.size(); i++ )
            var2TravId[i] = 0;
        travId = 1;
        coneRoot0 = coneRoot1 = -1;
    }
    assert( travId == 1 && coneRoot0 == -1 && coneRoot1 == -1 );
    useConeFanouts = true;
    coneFanoutHeads.growTo( nVars(), -1 );
    coneFanoutNext.growTo( 2*nVars(), -1 );
    coneFanoutPrev.growTo( 2*nVars(), -1 );
    coneRefs.growTo( nVars(), 0 );
    for ( int i = 0; i < count; i++ )
        coneRef( roots[i], 1 );
    for ( int i = 0; i < coneRoots.size(); i++ )
        coneRef( coneRoots[i], -1 );
    coneRoots.clear();
    for ( int i = 0; i < count; i++ )
        coneRoots.push( roots[i] );
}

inline void Solver::markCone( Var v ){
	if( var2TravId[v] >= travId )
		return;
	var2TravId[v] = travId;
	var2NodeData[v].sort = 0;
	Var var0, var1;
	var0 = getFaninVar0(v);
	var1 = getFaninVar1(v);
	if( !isTwoFanin(v) )
		return;
	markCone( var0 );
	markCone( var1 );
}

inline void Solver::inplace_sort( Var v ){
	Lit w, next, prev;
	prev= var2Fanout0[v];

	if( toLit(~0) == prev ) return;

	if( isRoundWatch(var(prev)) )
		var2NodeData[v].sort ++ ;

	if( toLit(~0) == (w = var2FanoutN[toInt(prev)]) )
		return;

	while( toLit(~0) != w ){
		next = var2FanoutN[toInt(w)];
		if( isRoundWatch(var(w)) )
			var2NodeData[v].sort ++ ;
		if( isRoundWatch(var(w)) && !isRoundWatch(var(prev)) ){
			var2FanoutN[toInt(w)] = var2Fanout0[v];
			var2Fanout0[v] = w;
			var2FanoutN[toInt(prev)] = next;
		} else
			prev = w;
		w = next;
	}
}

inline void Solver::prelocate( int base_var_num ){
	if( justUsage() ){
		var2FanoutN .prelocate( base_var_num << 1 );
		var2Fanout0 .prelocate( base_var_num );
		var2NodeData.prelocate( base_var_num );
		var2TravId  .prelocate( base_var_num );
		jheap       .prelocate( base_var_num );
		jlevel      .prelocate( base_var_num );
		jnext       .prelocate( base_var_num );
	}
	watches    .prelocate( base_var_num << 1 );
	watchesBin .prelocate( base_var_num << 1 );

	decision   .prelocate( base_var_num );
	trail      .prelocate( base_var_num );
	assigns    .prelocate( base_var_num );
	vardata    .prelocate( base_var_num );
	activity   .prelocate( base_var_num );


	seen       .prelocate( base_var_num );
	permDiff   .prelocate( base_var_num );
	polarity   .prelocate( base_var_num );
}


inline void Solver::markTill( Var v, int nlim ){
	if( var2TravId[v] == travId )
		return;

	vMarked.push(v);

	if( vMarked.size() >= nlim )
		return;
	if( var2TravId[v] == travId-1 || !isTwoFanin(v) )
		goto finalize;

	markTill( getFaninVar0(v), nlim );
	markTill( getFaninVar1(v), nlim );
finalize:
	var2TravId[v] = travId;
}

inline void Solver::markApprox( Var v0, Var v1, int nlim ){
    int i;
	if( travId <= 1 || nSkipMark>=4 || 0 == nlim )
		goto finalize;

	vMarked.shrink_( vMarked.size() );
	travId ++ ; // travId = t+1
	assert(travId>1);

	markTill(v0, nlim);
	if( vMarked.size() >= nlim )
		goto finalize;

	markTill(v1, nlim);
	if( vMarked.size() >= nlim )
		goto finalize;

	travId -- ; // travId = t
	for(i = 0; i < vMarked.size(); i ++){
		var2TravId  [ vMarked[i] ]      = travId;   // set new nodes to time t
		var2NodeData[ vMarked[i] ].sort = 0;
	}
	nSkipMark ++ ;
	return;
finalize:

	travId ++ ;
	nSkipMark = 0;
	markCone(v0);
	markCone(v1);
}

inline void Solver::loadJust_rec( Var v ){
	//assert( value(v) != G3_l_Undef );
	if( var2TravId[v] == travId || value(v) == G3_l_Undef )
		return;
	assert( var2TravId[v] == travId-1 );
	var2TravId[v] = travId;
	vMarked.push(v);

	if( !isTwoFanin(v) ){
		JustModel.push( mkLit( v, value(v) == G3_l_False ) );
		return;
	}
	loadJust_rec( getFaninVar0(v) );
	loadJust_rec( getFaninVar1(v) );
}
inline void Solver::loadJust(){
    int i;
	travId ++ ;
	JustModel.shrink_(JustModel.size());
	vMarked.shrink_(vMarked.size());
	JustModel.push(toLit(0));
	for(i = 0; i < assumptions.size(); i ++)
		loadJust_rec( var(assumptions[i]) );
	JustModel[0] = toLit( JustModel.size()-1 );
	travId -- ;
	for(i = 0; i < vMarked.size(); i ++)
		var2TravId[ vMarked[i] ] = travId;
}

};

ABC_NAMESPACE_IMPL_END

#endif
