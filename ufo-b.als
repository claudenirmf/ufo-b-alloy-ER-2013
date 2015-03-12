/*
==============================================
Unified Foundational Ontology (UFO)
Fragment B (Event Ontology)
Version 2.0
August, 2012

Ontology and Conceptual Modeling Research Group (NEMO)

Contributors: Giancarlo Guizzardi, Gerd Wagner, J.P.A. Almeida, 
                      Ricardo Falbo, Renata Guizzardi
==============================================
*/

//Event Extensional Mereology
abstract sig Event 
{
    start_point: one Int,
    end_point: one Int,
    before: set Event,
    meet: set Event,
    overlap: set Event,
    starts: set Event,
    during: set Event,
    finishes: set Event,
    equal: set Event, 
    pre_situation: Situation,
    pos_situation:Situation,
    causes: set Event,
    brings_about: set Situation,
    causally_contributes: set Event
}

sig SimpleEvent extends Event 
{
   dependentOf: one Object
}

sig ComplexEvent extends Event
{
    hasPart: some Event
}

fact 
{
	no x:Event | x in x.hasPart
	all x,y:ComplexEvent,z:Event | (y in x.hasPart) and (z in y.hasPart) implies   (z in x.hasPart)
	all x:ComplexEvent, y:ComplexEvent | (y in x.hasPart) implies (some z:Event | !(overlap[z,y]) and (z in x.hasPart))
	all x:ComplexEvent, y:SimpleEvent | (y in x.hasPart) implies (some z:Event | !(z=y) and (z in x.hasPart))
	all x,y:ComplexEvent | (all w:SimpleEvent | (w in x.hasPart) <=> (w in y.hasPart)) implies (x=y)
	all x,y:ComplexEvent | (all w:SimpleEvent | (w in x.hasPart) => (w in y.hasPart) and (!x=y)) implies (x in y.hasPart)  
}

pred overlap(x,y:Event)
{
	x in (y.hasPart) or (y in x.hasPart) or (some z:Event | (z in x.hasPart) and (z in y.hasPart))  
}

pred dependsSolelyOn(x:Event, o:Object)
{
    ((x in SimpleEvent) and (o=x.dependentOf)) or 
   ((x in ComplexEvent) and (all y:SimpleEvent | (y in x.hasPart) implies (o in y.dependentOf)))
}

pred dependsOn(x:Event, o:Object)
{
   (dependsSolelyOn[x,o] or (some y: Event | (y in x.hasPart) and (dependsSolelyOn[y,o])))
}

fact {all x, y:Event | overlap[x,y] implies overlap[y,x]} 

abstract sig Endurant
{
	presentIn: set Situation
}

sig Object extends Endurant
{
    plays: Role,
    created_by: set Event,
    terminated_by: set Event,
    changed_by: set Event
}

//Object Participation in Events

sig Participation in Event 
{
	kindOf: one ParticipationKind
}

fact
{     
   all x:Event | (x in Participation) <=> ((one o:Object | depx[x,o]))
}

pred depx (e:Event, o:Object)
{
     ((e in SimpleEvent) and (o in e.dependentOf)) or
     ((e in ComplexEvent) and (all x:SimpleEvent | x in e.hasPart implies (o in x.dependentOf)))
}

//RoleDifferentiation (Processual Roles) in Events
sig ParticipationKind {}
sig Role 
{
    inducedBy: one ParticipationKind
}

fact 
{
   all x:ParticipationKind | (some y:Participation |x in y.kindOf)
   all x:ParticipationKind | (some y:Role | x in y.inducedBy)
   all x:Role | (some y:Object | x in y.plays)
   all o:Object, p:SimpleEvent, k:ParticipationKind, r:Role | 
   ((o in p.dependentOf) and ((k in p.kindOf) or (some 
   c:Participation | (p in c.hasPart) and (k in c.kindOf))) and (k in 
   r.inducedBy))implies (r in o.plays)
   all r:Role, o:Object | (r in o.plays) implies 
   (some p:SimpleEvent, k:ParticipationKind | 
   ((o in p.dependentOf) and ((k in p.kindOf) or (some 
   c:Participation | (p in c.hasPart) and (k in c.kindOf))) and (k in 
   r.inducedBy)))
}

//Temporal Ordering (Allen Relations)

fun begin(e:Event): Int 
{
   e.start_point
}

fun end(e:Event) :Int
{
   e.end_point
}

fact 
{
    all x:Event | (begin[x] >= 0) and (end[x] >= 0) 
    all x:Event | (begin[x] < end [x])
    all x,y:Event | ((y in x.before) <=> (end[x] < begin[y]))
    all x,y:Event | ((y in x.meet) <=> (end[x] = begin[y]))
    all x,y:Event | ((y in x.overlap) <=> ((begin[x] < begin[y]) and (end[x] > begin[y]) and (end[x] < end[y])))
    all x,y:Event | ((y in x.starts) <=> ((begin[x] = begin[y])) and (end[x] < end[y]))
    all x,y:Event | ((y in x.during) <=> ((begin[x] > begin[y])) and (end[x] < end[y]))
    all x,y:Event | ((y in x.finishes) <=> ((begin[x] > begin[y])) and (end[x] = end[y]))
    all x,y:Event | ((y in x.equal) <=> (!(x=y) and (begin[x] = begin[y]) and (end[x] = end[y])))
    all x,y: Event | (y in x.hasPart) implies ((begin[x] <= begin[y]) and (end[x] >= end[y]))
    all x:ComplexEvent, t:Int | ((occurs_in[x,t]) implies (some y:Event | (y in x.hasPart) and occurs_in[y,t]))  
}

pred occurs_in(e:Event, t:Int)
{
    (t>=begin[e]) and (t<=end[e])
}

//Situations

sig Situation
{
  obtains: one Int,
  enables: set Event,
  activates: set Disposition
}

fact
{
   all s:Situation | s.obtains >= 0
   all s:Situation,e:Event | (s in e.pre_situation) implies ((begin[e] in s.obtains) and (e in s.enables))
   all s:Situation,e:Event | (e in s.enables) implies (s in e.pre_situation)  
   all e:Event | some s:Situation | s in e.pre_situation
   all s:Situation,e:Event | (s in e.pos_situation) implies ((end[e] in s.obtains) and (s in e.brings_about))  
   all s:Situation,e:Event | (s in e.brings_about) implies (s in e.pos_situation)  
   all e:Event | some s:Situation | s in e.pos_situation  
   all x,y: Event | (y in x.causes) <=> (some s:Situation | (s in x.brings_about) and (y in s.enables))
   all x,y:Event | (y in x.^(causes)) implies (y in x.causally_contributes)
   all x,y:Event | (y in x.causally_contributes) implies (y in x.^(causes))
}

//Qualities
sig QualityKind {}
sig QualityStructure 
{
    associated_with: one QualityKind
}
sig Quale
{
  memberOf: one QualityStructure,
  valueOf: set Quality
}

sig Quality 
{
    inheresIn: one Event,
    instantiates: one QualityKind
}

fact
{
   all x:QualityKind | some y:Quality | x in y.instantiates
   all x:QualityStructure | some y:Quale | x in y.memberOf
   all x:QualityKind| some y:QualityStructure | x in y.associated_with
   all x:Quality,q:Quale | (x in q.valueOf) implies 
   (some QU:QualityKind, QS:QualityStructure | (QU in x.instantiates) and (QU    
   in QS.associated_with) and (QS in q.memberOf))
   all x:Quality,  QU:QualityKind, QS:QualityStructure | 
   (QU in x.instantiates) and (QU in QS.associated_with) implies 
   (one q:Quale | (QS in q.memberOf) and (x in q.valueOf))
   all x,y:Quality,z:Event,w,q:QualityKind | (z in x.inheresIn) and (z in 
   y.inheresIn) 
   and (w in x.instantiates) and (q in y.instantiates) and (w=q) implies (x=y)
   all x:Quality,y,z:Quale,w:QualityStructure | 
   ((x in y.valueOf) and (x in z.valueOf) and (w in y.memberOf) and (w in 
   z.memberOf)) implies (y=z)
}

//Dispositions
sig Disposition extends Endurant
{
    inheresIn: one Object,
    manifested_by: one SimpleEvent
}

fact
{
    all o:Object | some d:Disposition | (o in d.inheresIn)
    all d:Disposition | some s:Situation | (d in s.activates)
    all d:Disposition, s:Situation, e:SimpleEvent | ((d in s.activates) and (e in d.manifested_by)) implies (e in s.enables) 
    all d:Disposition, e:SimpleEvent, o:Object | ((e in d.manifested_by) and (o in d.inheresIn)) implies (o in e.dependentOf)
    all e:SimpleEvent | one d:Disposition | (e in d.manifested_by)
    all e:Event, d:Disposition | (e in d.manifested_by) implies 
    (all s1,s2:Situation | ((s1 in e.pre_situation) implies (s1 in d.presentIn)) and ((s2 in e.pos_situation) implies (s2 in d.presentIn)))
    all d:Disposition, o:Object | (o in d.inheresIn) implies
    (all s:Situation | (s in d.presentIn) implies (s in o.presentIn)) 
}

//Creation, Termination and Change

fact
{
  all o:Object, e:Event | (e in o.created_by) implies 
  (all s1, s2:Situation | (s1 in e.pre_situation) and (s2 in e.pos_situation)  
   implies (!(s1 in o.presentIn) and (s2 in o.presentIn) and dependsOn[e,o]))
   
  all o:Object, e:Event | (e in o.terminated_by) implies 
  (all s1, s2:Situation | (s1 in e.pre_situation) and (s2 in e.pos_situation)  
   implies ((s1 in o.presentIn) and !(s2 in o.presentIn) and dependsOn[e,o]))
   
  all o:Object, e:Event | (e in o.changed_by) implies 
  (all s1, s2:Situation | (s1 in e.pre_situation) and (s2 in e.pos_situation)  
  implies ((s1 in o.presentIn) and (s2 in o.presentIn) and dependsOn[e,o]
  and (some d:Disposition | (o in d.inheresIn) and ((!(s1 in d.presentIn) and (s2 in d.presentIn)) 
  or ((s1 in d.presentIn) and !(s2 in d.presentIn))))))
}

pred show {}
run show for 3



