"
I model the JITDomain state of one RISC-V hart for the Unicorn simulator, which does not know the extension.
UnicornRISCVSimulator hands me the instructions Unicorn rejects; I emulate the ones of the extension:

- domcall, domret and domlpad (custom-2), with the Domain Return Stack kept here, not in simulated memory:
  this models the DRS key, which no ordinary or typed access may touch;
- the typed loads and stores dl*/ds* (custom-0/1) as plain accesses: keys and rights are not modelled;
- every CSR instruction on udsp (the U-mode alias of dsp, VM domain (DOM0) only, whose writes must stay in [dsp, dspbase])
  and csrr of curdom. dstatus.EN is taken as 1.

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
		'dspbase',
		'drs',
		'gates',
		'events'
	],
	#category : 'VMMakerTests-Unicorn',
	#package : 'VMMakerTests',
	#tag : 'Unicorn'
}

{ #category : 'constants' }
JITDomainHartState class >> curdomCSR [

	^ 16rCC0
]

{ #category : 'constants' }
JITDomainHartState class >> udspCSR [

	"Provisional, see CogOutOfLineLiteralsRiscV64Compiler class >> initialize"
	^ 16r8C6
]

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

	"Without a DRS (dspbase at its reset value 0, as for a new thread) the push faults"
	(dspbase = 0 or: [ dsp \\ 8 ~= 0 ]) ifTrue: [ JITDomainFault signal: #DRS pc: pc ].
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

{ #category : 'accessing' }
JITDomainHartState >> dspbase [

	^ dspbase
]

{ #category : 'accessing' }
JITDomainHartState >> dspbase: anAddress [

	"The top of the DRS, set by S mode"
	dspbase := anAddress
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
	(opcode = 2r0001011 and: [ funct3 ~= 7 ]) ifTrue: [ self typedLoadAt: pc word: word in: aSimulator. ^ true ].
	(opcode = 2r0101011 and: [ funct3 < 4 ]) ifTrue: [ self typedStoreAt: pc word: word in: aSimulator. ^ true ].
	opcode = 2r1110011 ifTrue: [ ^ self emulateCSRAt: pc word: word in: aSimulator ].
	^ false
]

{ #category : 'emulation' }
JITDomainHartState >> emulateCSRAt: pc word: word in: aSimulator [

	| csr funct3 rs1 rd old source new |
	csr := word >> 20.
	funct3 := word >> 12 bitAnd: 7.
	rs1 := word >> 15 bitAnd: 31.
	rd := word >> 7 bitAnd: 31.
	csr = self class curdomCSR ifTrue: [
		(funct3 = 2 and: [ rs1 = 0 ]) ifFalse: [ ^ false ].
		self register: rd put: curdom in: aSimulator.
		aSimulator instructionPointerRegisterValue: pc + 4.
		^ true ].
	(csr = self class udspCSR and: [ (funct3 bitAnd: 3) ~= 0 ]) ifFalse: [ ^ false ].
	curdom = 0 ifFalse: [ JITDomainFault signal: #DSP pc: pc ].
	old := dsp.
	"csrrs/csrrc with rs1 = x0 or a zero immediate only read"
	((funct3 bitAnd: 3) = 1 or: [ rs1 ~= 0 ]) ifTrue: [
		source := funct3 >= 4
			ifTrue: [ rs1 ]
			ifFalse: [ self register: rs1 in: aSimulator ].
		new := (funct3 bitAnd: 3) = 1
			ifTrue: [ source ]
			ifFalse: [
				(funct3 bitAnd: 3) = 2
					ifTrue: [ dsp bitOr: source ]
					ifFalse: [ dsp bitClear: source ] ].
		"Only upwards, never past the top of the DRS: popped records cannot be replayed"
		(new between: dsp and: dspbase) ifFalse: [ JITDomainFault signal: #DSPRANGE pc: pc ].
		dsp := new.
		events add: { #udsp. pc. dsp } ].
	self register: rd put: old in: aSimulator.
	aSimulator instructionPointerRegisterValue: pc + 4.
	^ true
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
	dspbase := 0.
	drs := Dictionary new.
	events := OrderedCollection new.
	"dgate as Cog configures it: the VM domain (0) and the JIT domain (1) may call each other, and the VM
	 domain itself (machine code still runs there when it exits through a gate), nothing else"
	gates := (1 to: 8) collect: [ :i | Set new ].
	self allowCallsFrom: 0 to: 1.
	self allowCallsFrom: 1 to: 0.
	self allowCallsFrom: 0 to: 0
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

{ #category : 'emulation' }
JITDomainHartState >> signExtend: aValue bits: aNumber [

	^ aValue >= (1 << (aNumber - 1))
		ifTrue: [ aValue - (1 << aNumber) ]
		ifFalse: [ aValue ]
]

{ #category : 'emulation' }
JITDomainHartState >> typedLoadAt: pc word: word in: aSimulator [

	| funct3 size address value |
	funct3 := word >> 12 bitAnd: 7.
	size := 1 << (funct3 bitAnd: 3).
	address := (self register: (word >> 15 bitAnd: 31) in: aSimulator)
		+ (self signExtend: word >> 20 bits: 12) \\ (2 raisedTo: 64).
	value := (aSimulator memoryAt: address readNext: size) integerAt: 1 size: size signed: funct3 < 4.
	self register: (word >> 7 bitAnd: 31) put: value in: aSimulator.
	events add: { #typedLoad. pc. address. size }.
	aSimulator instructionPointerRegisterValue: pc + 4
]

{ #category : 'emulation' }
JITDomainHartState >> typedStoreAt: pc word: word in: aSimulator [

	| size offset address bytes |
	size := 1 << (word >> 12 bitAnd: 3).
	offset := self signExtend: (word >> 25 << 5 bitOr: (word >> 7 bitAnd: 31)) bits: 12.
	address := (self register: (word >> 15 bitAnd: 31) in: aSimulator) + offset \\ (2 raisedTo: 64).
	bytes := ByteArray new: 8.
	bytes integerAt: 1 put: (self register: (word >> 20 bitAnd: 31) in: aSimulator) size: 8 signed: false.
	aSimulator memoryAt: address write: (bytes first: size) size: size.
	events add: { #typedStore. pc. address. size }.
	aSimulator instructionPointerRegisterValue: pc + 4
]
