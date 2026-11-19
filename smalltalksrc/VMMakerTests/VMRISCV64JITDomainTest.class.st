"
I test the JITDomain instructions of the RISC-V backend: their encodings against the assembler, and their execution
under the JITDomain model of UnicornRISCVSimulator (see JITDomainHartState).
"
Class {
	#name : 'VMRISCV64JITDomainTest',
	#superclass : 'VMSimpleStackBasedCogitAbstractTest',
	#category : 'VMMakerTests-JitTests',
	#package : 'VMMakerTests',
	#tag : 'JitTests'
}

{ #category : 'tests' }
VMRISCV64JITDomainTest class >> wordSizeParameters [

	^ ParametrizedTestMatrix new
		addCase: { #ISA -> #'riscv64' . #wordSize -> 8 };
		yourself
]

{ #category : 'helpers' }
VMRISCV64JITDomainTest >> compileDomainCallTo: anAddress domain: aDomain label: aLabel [

	"Answer the start and end addresses of: TempReg := anAddress; domcall TempReg; ClassReg := 7"

	| start end |
	start := self compile: [
		cogit MoveCw: anAddress R: TempReg.
		cogit gen: (self opcode: #DomCallR) operand: TempReg operand: aDomain operand: aLabel.
		cogit MoveCq: 7 R: ClassReg.
		end := cogit Label ] bytecodes: 10.
	^ start -> end address
]

{ #category : 'helpers' }
VMRISCV64JITDomainTest >> compileDomainCallee: aDomain label: aLabel [

	"A callee entered by domcall: domlpad; ReceiverResultReg := 42; domret"

	^ self compile: [
		cogit gen: (self opcode: #DomLpad) operand: aDomain operand: aLabel.
		cogit MoveCq: 42 R: ReceiverResultReg.
		cogit gen: (self opcode: #DomRet) ] bytecodes: 10
]

{ #category : 'helpers' }
VMRISCV64JITDomainTest >> compileWithEnd: aBlock [

	| start end |
	start := self compile: [ aBlock value. end := cogit Label ] bytecodes: 10.
	^ start -> end address
]

{ #category : 'accessing' }
VMRISCV64JITDomainTest >> hart [

	^ machineSimulator jitDomain
]

{ #category : 'helpers' }
VMRISCV64JITDomainTest >> opcode: aSymbol [

	^ CogOutOfLineLiteralsRiscV64Compiler classPool at: aSymbol
]

{ #category : 'helpers' }
VMRISCV64JITDomainTest >> runFromTo: startToEnd [

	machineSimulator startAt: startToEnd key until: startToEnd value timeout: 0 count: 1000
]

{ #category : 'helpers' }
VMRISCV64JITDomainTest >> should: aBlock faultWith: aSubcode [

	| fault |
	fault := nil.
	aBlock on: JITDomainFault do: [ :e | fault := e ].
	self assert: fault notNil description: 'no domain CFI fault'.
	self assert: fault subcode equals: aSubcode
]

{ #category : 'running' }
VMRISCV64JITDomainTest >> setUp [

	super setUp.
	self hart dsp: 16r10000
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testDomainCallFromTheWrongDomainFaultsWithGate [

	"dgate allows only calls between the VM domain (0) and the JIT domain (1), so a call into domain 2 faults"

	| callee |
	callee := self compileDomainCallee: 2 label: 0.
	self should: [ self runFromTo: (self compileDomainCallTo: callee domain: 2 label: 0) ] faultWith: #GATE
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testDomainCallReachesThePadAndDomainReturnComesBack [

	| callee |
	callee := self compileDomainCallee: 1 label: 3.
	self runFromTo: (self compileDomainCallTo: callee domain: 1 label: 3).

	self assert: machineSimulator receiverRegisterValue equals: 42.
	self assert: machineSimulator classRegisterValue equals: 7.
	self assert: self hart curdom equals: 0.
	self assert: self hart drsDepth equals: 0.
	self assert: self hart dsp equals: 16r10000.
	self assert: (self hart events collect: [ :e | e first ]) asArray equals: #( #domcall #domret ).
	self assert: (self hart events first at: 5) equals: 1
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testDomainCallToAPadOfAnotherDomainFaultsWithLpad [

	| callee |
	callee := self compileDomainCallee: 0 label: 0.
	self should: [ self runFromTo: (self compileDomainCallTo: callee domain: 1 label: 0) ] faultWith: #LPAD
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testDomainCallToAPadWithAnotherLabelFaultsWithLpad [

	| callee |
	callee := self compileDomainCallee: 1 label: 3.
	self should: [ self runFromTo: (self compileDomainCallTo: callee domain: 1 label: 4) ] faultWith: #LPAD
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testDomainCallToCodeWithoutAPadFaultsWithLpad [

	| callee |
	callee := self compile: [ cogit MoveCq: 42 R: ReceiverResultReg. cogit gen: (self opcode: #DomRet) ] bytecodes: 10.
	self should: [ self runFromTo: (self compileDomainCallTo: callee domain: 1 label: 0) ] faultWith: #LPAD
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testDomainReturnWithAnEmptyStackFaultsWithDrs [

	self should: [ self runFromTo: (self compileWithEnd: [ cogit gen: (self opcode: #DomRet) ]) ] faultWith: #DRS
]

{ #category : 'tests - encoding' }
VMRISCV64JITDomainTest >> testEncodingsMatchTheAssembler [

	"Expected words from riscv64-linux-gnu-as with the .insn macros of jitdomain.h"

	| backEnd |
	backEnd := cogit backEnd.
	self assert: (backEnd domainLandingPad: 1 label: 0) equals: 16r2000205B.
	self assert: (backEnd domainLandingPad: 0 label: 5) equals: 16r0050205B.
	self assert: (backEnd domainLandingPad: 7 label: 511) equals: 16rFFF0205B.
	self assert: (backEnd domainCallTo: 6 domain: 1 label: 3) equals: 16r2033005B.
	self assert: backEnd domainReturn equals: 16r0000105B.
	self assert: (backEnd typedLoadDoubleWordFromAddressInRegister: 26 withOffset: -2048 toRegister: 10) equals: 16r800D350B.
	self assert: (backEnd typedLoadDoubleWordFromAddressInRegister: 26 withOffset: 2047 toRegister: 10) equals: 16r7FFD350B.
	self assert: (backEnd typedStoreDoubleWordFromRegister: 11 toAddressInRegister: 26 withOffset: 8) equals: 16r00BD342B.
	self assert: (backEnd typedStoreDoubleWordFromRegister: 11 toAddressInRegister: 26 withOffset: -8) equals: 16rFEBD3C2B.
	self assert: (backEnd csrReadWrite: 16r8C6 register: 5 into: 0) equals: 16r8C629073.
	self assert: (backEnd csrRead: 16r8C6 into: 5) equals: 16r8C6022F3
]

{ #category : 'tests - encoding' }
VMRISCV64JITDomainTest >> testInstructionsAreConcretizedInFourBytes [

	| start words |
	start := self compile: [
		cogit gen: (self opcode: #DomLpad) operand: 1 operand: 0.
		cogit gen: (self opcode: #DomCallR) operand: 6 operand: 1 operand: 3.
		cogit gen: (self opcode: #DomRet).
		cogit gen: (self opcode: #MoveDMwrR) operand: -2048 operand: 26 operand: 10.
		cogit gen: (self opcode: #MoveRDMwr) operand: 11 operand: 8 operand: 26.
		cogit gen: (self opcode: #MoveRUdsp) operand: 5.
		cogit gen: (self opcode: #MoveUdspR) operand: 5 ] bytecodes: 10.
	words := (0 to: 6) collect: [ :i | (machineSimulator memoryAt: start + (4 * i) readNext: 4) unsignedLongAt: 1 bigEndian: false ].
	self assert: words asArray equals: #( 16r2000205B 16r2033005B 16r0000105B 16r800D350B 16r00BD342B 16r8C629073 16r8C6022F3 )
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testPadReachedWithoutDomainCallIsANop [

	self runFromTo: (self compileWithEnd: [
		cogit gen: (self opcode: #DomLpad) operand: 1 operand: 3.
		cogit MoveCq: 42 R: ReceiverResultReg ]).
	self assert: machineSimulator receiverRegisterValue equals: 42.
	self assert: self hart curdom equals: 0
]

{ #category : 'tests - execution' }
VMRISCV64JITDomainTest >> testWildcardPadAcceptsAnyLabel [

	| callee |
	callee := self compileDomainCallee: 1 label: 0.
	self runFromTo: (self compileDomainCallTo: callee domain: 1 label: 5).
	self assert: machineSimulator receiverRegisterValue equals: 42.
	self assert: self hart drsDepth equals: 0
]
