enum ComponentType { Holder, IdentityWallet, Issuer, Verifier, DistributedLedger }
enum DataType { IdentityAttribute, SSI, IdentityClaim, VerifiableClaim, IdentityPresentation, PublicKey, PrivateKey, ProofSchema, DID, DIDDocument, ServiceToken }
enum SharingForm { Raw, Implicit, Broadcast, Revoke }

abstract sig Component { compType: one ComponentType, own: set DataObject  }
abstract sig DataObject { dataType: one DataType, ownedBy: one Component }

sig State { component: set Component }
sig Event {
	form: one SharingForm,
	consigner: set Component,
	consignee: set Component,
	sharedData: set DataObject
}

one sig SDSM {
	s0: set State,
	states: set State,
	events: set Event,
	transitions: State -> Event -> State
}

fun initialState : State { SDSM.s0 }
fun allStates : State { SDSM.states }
fun allEvents : Event { SDSM.events }
fun nextState : State -> Event -> State { SDSM.transitions }

pred init [s: State] {
	s.component.own = none
}

pred transition [a, b: State, e: Event] {
	raw_sharing [a, b, e] or
	implicit_sharing [a, b, e] or
	broadcast_sharing [a, b, e] or
	revoke_sharing [a, b, e]
}

fact {
	// Set the initial states
	all s: State | s in initialState iff init [s]
	// Set the possible transitions in the SSI data sharing model
	all a, b: State, e: Event | a->e->b in nextState iff transition [a, b, e]
	// States are always having transitions
	all a, b: State, e: Event | a in allStates and b in allStates and e in allEvents implies a->e->b in nextState
	// Implication of identical states
	all a, b: State | a.component = b.component implies a = b
	// Implication of identical events
	all a, b: Event | a.form = b.form and a.consigner = b.consigner and a.consignee = b.consignee and a.sharedData = b.sharedData implies a = b
	// All events are contained in the event set of the SSI data sharing model
	all e: Event | e in allEvents
	// All states are contained in the system state set of the SSI data sharing model
	all s: State | s in allStates
	// There must not be an empty event occurred
	all e: Event | e.consigner != none and e.consignee != none and e.sharedData != none
	// All sharing must be under a valid protocol
 	all e: Event | validProtocol [e]

	one c : Component | c.compType = DistributedLedger

	all e: Event, d: DataObject | d in e.sharedData and d.dataType != PrivateKey  
}

pred validProtocol [e: Event] {
	all a, b: Component, d: DataObject | a.compType = Holder and b.compType = IdentityWallet and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = IdentityAttribute + IdentityClaim
	all a, b: Component, d: DataObject | a.compType = IdentityWallet and b.compType = DistributedLedger and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DIDDocument + PublicKey
	all a, b: Component, d: DataObject | a.compType = IdentityWallet and b.compType = Issuer and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DID + IdentityClaim
	all a, b: Component, d: DataObject | a.compType = Issuer and b.compType = DistributedLedger and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DIDDocument + PublicKey + ProofSchema
	all a, b: Component, d: DataObject | a.compType = Issuer and b.compType = IdentityWallet and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DID + VerifiableClaim
	all a, b: Component, d: DataObject | a.compType = IdentityWallet and b.compType = Verifier and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DID + IdentityPresentation
	all a, b: Component, d: DataObject | a.compType = Verifier and b.compType = DistributedLedger and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DIDDocument + PublicKey + IdentityPresentation
	all a, b: Component, d: DataObject | a.compType = Verifier and b.compType = IdentityWallet and a in e.consigner and b in e.consignee and d in e.sharedData 
		implies d.dataType = DID + ServiceToken
}

-- -----------------------
-- Transitional Relations
pred raw_sharing [a, b: State, e: Event] {
	e.form = Raw
	pre_raw [a, e]
	post_raw [a, b, e]
}

pred pre_raw [a: State, e: Event] {
	e.consigner in a.component
	// The consigner owns the data object before sharing
	all c : Component, d: DataObject | c in e.consigner and d in e.sharedData implies c in a.component and d in c.own
	// The shared data must not be identity claims
	all d : DataObject | d in e.sharedData implies d.dataType != IdentityClaim
}

pred post_raw [a, b: State, e: Event] {
	e.consigner in b.component
	e.consignee in b.component
	// All shared data must be persisted in the consignee after sharing
	all c : Component, d : DataObject | c in e.consignee and c in b.component and d in e.sharedData implies d in c.own
}

pred implicit_sharing [a, b: State, e: Event] {
	e.form = Implicit
	pre_implicit [a, e]
	post_implicit [a, b, e]
}

pred pre_implicit [a: State, e: Event] {
	e.consigner in a.component
	// The consigner owns the data object before sharing
	all c : Component, d: DataObject | c in e.consigner and d in e.sharedData implies c in a.component and d in c.own
	// The shared data must be identity claims or verifiable claims
	all d : DataObject | d in e.sharedData implies d.dataType = IdentityClaim + VerifiableClaim
}

pred post_implicit [a, b: State, e: Event] {
	e.consigner in b.component
	e.consignee in b.component
	// All shared data must be persisted in the consignee after sharing
	all c : Component, d : DataObject | c in e.consignee and c in b.component and d in e.sharedData implies d in c.own
}

pred broadcast_sharing [a, b: State, e: Event] {
	e.form = Broadcast
	pre_broadcast [a, e]
	post_broadcast [a, b, e]
}

pred pre_broadcast [a: State, e: Event] {
	e.consigner in a.component
	// The consignee must be the distributed ledger 
	all c : Component | c in e.consignee implies c.compType = DistributedLedger
	// Proof schema, DID document, and Public are only data objects that can be broadcasted 
	all d : DataObject | d in e.sharedData implies d.dataType = ProofSchema + DIDDocument + PublicKey
}

pred post_broadcast [a, b: State, e: Event] {
	e.consigner in b.component
	e.consignee in b.component
	// All shared dat must be persisted in the distributed ledger after sharing
	all c : Component, d : DataObject | c in b.component and d in e.sharedData and c.compType = DistributedLedger implies d in c.own 
}

pred revoke_sharing [a, b: State, e: Event] {
	e.form = Revoke
	pre_revoke [a, e]
	post_revoke [a, b, e]
}

pred pre_revoke [a: State, e: Event] {
	e.consigner in a.component
	// The consigner must have the right to revoke the sharing by holding the revoking data object
	all c: Component, d: DataObject | c in a.component and c in e.consigner implies d in c.own
	// The consignee must hold the revoking data object first
	all c: Component, d: DataObject | c in a.component and c in e.consignee implies d in c.own
}

pred post_revoke [a, b: State, e: Event] {
	e.consigner in b.component
	e.consignee in b.component
	// The shared data must be removed from the consignee right after the sharing
	no c: Component, d: DataObject | c in b.component and c in e.consignee and d in e.sharedData implies d in c.own
}

-- -----------------
-- Specification of Information Security and Privacy in the SSI data sharing model

// IP3. Single Source - Holders and identity wallets must always be consigners if identity attributes and identity claims are involved in the SSI data sharing event
pred singleSourceProperty {
	all e: Event, a, b: Component, d: DataObject | d in e.sharedData and a in e.consigner and b in e.consignee
		implies a.compType != Holder and b.compType = IdentityWallet and d.dataType = IdentityAttribute + IdentityClaim
}

// IP6. Decentralized - Veriﬁable claims must be created only after proof scheme is already shared on the distributed ledger.
pred decentralizedProperty {
	all e: Event, a, b: State, c: Component, d1, d2: DataObject | transition [a, b, e] and c in a.component and c.compType = DistributedLedger
		 and d1.dataType = ProofSchema and d2.dataType = VerifiableClaim implies d1 not in c.own and d2 in e.sharedData 
}

// IP11. Access Control - Identity attributes and identity claims must always be handled by the corresponding identity wallet and cannot be revoked.
pred accessControlProperty {
	no e: Event, a, b: Component, d: DataObject | b in e.consigner and a in e.consignee and d in e.sharedData and d.dataType = IdentityAttribute + SSI
		implies a.compType = IdentityWallet and e.form = Revoke and b.compType != Holder
}

// IP13. Persistence - Data objects handled by a component must be persisted until the revocation sharing form is held by the component as a consignee.
pred persistenceProperty {
	all s1, s2: State, e: Event, c: Component, d: DataObject | c in s1.component and transition [s1, s2, e] and e.form = Revoke and c in e.consigner implies
		d not in c.own
}

// IP17. Data Minimization - In all events in the implicit sharing form, the sharing data must be either an identity claim or a verifiable claim. 
pred dataMinimizationProperty {
	always all e: Event, d: DataObject | d in e.sharedData and d.dataType != IdentityClaim + VerifiableClaim implies e.form = Implicit
}

// IP25. Data Integrity - An event of sharing DID must always come before other SSI data sharing events for a pair of given components.
pred dataIntegrityProperty {
	all s1, s2: State, e: Event, c1, c2: Component, d1, d2: DataObject | transition [s1, s2, e] and c1 in s1.component and c2 in s1.component and
		c1 in e.consigner and c2 in e.consignee implies d1 not in c1.own and d2 not in c2.own and d1.ownedBy = c2 and d2.ownedBy = c1 and 
		d1.dataType = DID and d2.dataType = DID
}

// IP31. Key Protection - All private keys must not be shared or involved in any SSI sharing event except the self-transition that the consigner and consignee are identical. 
pred keyProtectionProperty {
	all e: Event, d: DataObject, c: Component | c in e.consigner and c not in e.consignee and d in e.sharedData implies d.dataType = PrivateKey
}

// IP39. Use and Disclosure Limitation - Consignees must not share the received data objects to others (without the consent of their owners).
pred useDisclosureLimitProperty {
	all s1, s2, s3: State, e1, e2: Event, c: Component, d: DataObject | transition [s1, s2, e1] and transition [s2, s3, e2] implies c in s2.component and c in e1.consignee and
		c in s3.component and d in e1.sharedData and c in e2.consigner and d in e2.sharedData and d.dataType != IdentityPresentation
}

pred allProperties {
	singleSourceProperty 
	decentralizedProperty 
	accessControlProperty
	persistenceProperty
	dataMinimizationProperty
	dataIntegrityProperty
	keyProtectionProperty
	useDisclosureLimitProperty
}

run {} for exactly 20 Component, exactly 20 DataObject, exactly 30 State, exactly 29 Event
