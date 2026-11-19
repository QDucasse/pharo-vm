"
I model the JITDomain state of one RISC-V hart for the Unicorn simulator, which does not know the extension.
UnicornRISCVSimulator hands me the instructions Unicorn rejects; I emulate the ones of the extension:

- domcall, domret and domlpad (custom-2), with the Domain Return Stack kept here, not in simulated memory:
  this models the DRS key, which no ordinary or typed access may touch.

A domcall checks dgate, pushes the DRS and then checks at once that its target is a matching, 4-byte aligned domlpad,
which it executes: the pad is the next instruction the hart would fetch. Violations signal JITDomainFault.
Every transition is logged in events for the tests.
"
Class {
	#name : 'JITDomainHartState',
	#superclass : 'Object',
	#instVars : [
		'curdom',
		'dsp',
		'drs',
		'gates',
		'events'
	],
	#category : 'VMMakerTests-Unicorn',
	#package : 'VMMakerTests',
	#tag : 'Unicorn'
}

{ #category : 'accessing' }
JITDomainHartState >> allowCallsFrom: fromDomain to: toDomain [

	(gates at: fromDomain + 1) add: toDomain
]

{ #category : 'accessing' }
JITDomainHartState >> curdom [

	^ curdom
]

{ #category : 'accessing' }
JITDomainHartState >> curdom: aDomain [

	curdom := aDomain
]

{ #category : 'emulation' }
JITDomainHartState >> domainCallAt: pc word: word in: aSimulator [

	| immediate domain label target |
	immediate := word >> 20.
	domain := immediate >> 9.
	label := immediate bitAnd: 16r1FF.
	((gates at: curdom + 1) includes: domain) ifFalse: [ JITDomainFault signal: #GATE pc: pc ].
	target := (self register: (word >> 15 bitAnd: 31) in: aSimulator) bitClear: 1.

	dsp \\ 8 = 0 ifFalse: [ JITDomainFault signal: #DRS pc: pc ].
	dsp := dsp - 8 \\ (2 raisedTo: 64).
	drs at: dsp put: pc + 4 -> curdom.
	self register: (word >> 7 bitAnd: 31) put: pc + 4 in: aSimulator.

	"The pending entry: the next fetch must be a matching domlpad"
	(target \\ 4 = 0 and: [ self isPadAt: target forDomain: domain label: label in: aSimulator ])
		ifFalse: [ JITDomainFault signal: #LPAD pc: target ].
	events add: { #domcall. pc. target. curdom. domain. label }.
	curdom := domain.
	aSimulator instructionPointerRegisterValue: target + 4
]

{ #category : 'emulation' }
JITDomainHartState >> domainReturnAt: pc in: aSimulator [

	| record |
	dsp \\ 8 = 0 ifFalse: [ JITDomainFault signal: #DRS pc: pc ].
	record := drs removeKey: dsp ifAbsent: [ JITDomainFault signal: #DRS pc: pc ].
	dsp := dsp + 8 \\ (2 raisedTo: 64).
	events add: { #domret. pc. record key. curdom. record value }.
	curdom := record value.
	aSimulator instructionPointerRegisterValue: record key
]

{ #category : 'accessing' }
JITDomainHartState >> drsDepth [

	^ drs size
]

{ #category : 'accessing' }
JITDomainHartState >> dsp [

	^ dsp
]

{ #category : 'accessing' }
JITDomainHartState >> dsp: anAddress [

	dsp := anAddress
]

{ #category : 'emulation' }
JITDomainHartState >> emulate: word at: pc in: aSimulator [

	"Emulate word, the instruction at pc, if it belongs to the extension. Answer whether it did."

	| opcode funct3 |
	opcode := word bitAnd: 16r7F.
	funct3 := word >> 12 bitAnd: 7.
	opcode = 2r1011011 ifTrue: [
		funct3 = 0 ifTrue: [ self domainCallAt: pc word: word in: aSimulator. ^ true ].
		(funct3 = 1 and: [ word = 16r105B ]) ifTrue: [ self domainReturnAt: pc in: aSimulator. ^ true ].
		(funct3 = 2 and: [ (word bitAnd: 16rF8F80) = 0 ]) ifTrue: [
			"A pad reached without a domcall is a nop"
			events add: { #domlpad. pc. curdom }.
			aSimulator instructionPointerRegisterValue: pc + 4.
			^ true ].
		^ false ].
	^ false
]

{ #category : 'accessing' }
JITDomainHartState >> events [

	^ events
]

{ #category : 'initialization' }
JITDomainHartState >> initialize [

	super initialize.
	curdom := 0.
	dsp := 0.
	drs := Dictionary new.
	events := OrderedCollection new.
	"dgate as Cog configures it: the VM domain (0) and the JIT domain (1) may call each other, nothing else"
	gates := (1 to: 8) collect: [ :i | Set new ].
	self allowCallsFrom: 0 to: 1.
	self allowCallsFrom: 1 to: 0
]

{ #category : 'emulation' }
JITDomainHartState >> isPadAt: address forDomain: domain label: label in: aSimulator [

	| word padImmediate |
	word := (aSimulator memoryAt: address readNext: 4) unsignedLongAt: 1 bigEndian: false.
	(word bitAnd: 16rFFFFF) = 16r0205B ifFalse: [ ^ false ].
	padImmediate := word >> 20.
	^ padImmediate >> 9 = domain and: [ (padImmediate bitAnd: 16r1FF) = 0 or: [ (padImmediate bitAnd: 16r1FF) = label ] ]
]

{ #category : 'emulation' }
JITDomainHartState >> register: aNumber in: aSimulator [

	aNumber = 0 ifTrue: [ ^ 0 ].
	^ aSimulator readRegister: (UcRISCVRegisters perform: ('x' , aNumber printString) asSymbol)
]

{ #category : 'emulation' }
JITDomainHartState >> register: aNumber put: aValue in: aSimulator [

	aNumber = 0 ifTrue: [ ^ self ].
	aSimulator
		writeRegister: (UcRISCVRegisters perform: ('x' , aNumber printString) asSymbol)
		value: (aValue \\ (2 raisedTo: 64))
]
