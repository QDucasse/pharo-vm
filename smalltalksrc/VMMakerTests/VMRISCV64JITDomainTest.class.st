"
I test the JITDomain instructions of the RISC-V backend: their encodings against the assembler.
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
VMRISCV64JITDomainTest >> opcode: aSymbol [

	^ CogOutOfLineLiteralsRiscV64Compiler classPool at: aSymbol
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
	self assert: backEnd domainReturn equals: 16r0000105B
]

{ #category : 'tests - encoding' }
VMRISCV64JITDomainTest >> testInstructionsAreConcretizedInFourBytes [

	| start words |
	start := self compile: [
		cogit gen: (self opcode: #DomLpad) operand: 1 operand: 0.
		cogit gen: (self opcode: #DomCallR) operand: 6 operand: 1 operand: 3.
		cogit gen: (self opcode: #DomRet) ] bytecodes: 10.
	words := (0 to: 2) collect: [ :i | (machineSimulator memoryAt: start + (4 * i) readNext: 4) unsignedLongAt: 1 bigEndian: false ].
	self assert: words asArray equals: #( 16r2000205B 16r2033005B 16r0000105B )
]
