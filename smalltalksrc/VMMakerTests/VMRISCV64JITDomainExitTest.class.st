"
I test how machine code leaves for the VM under JITDOMAIN: each trampoline is a gate, entered through a thunk.

- Gates (the trampolines, the enilopmarts and the routines called from C) stay at the start of the code zone.
  A gate starts with domlpad 0, 1 and returns with domret.
- From the next page boundary on, the fixed code area holds a thunk per gate and the helpers machine code calls
  without leaving. A thunk is:
      auipc/addi x5, gate
      domcall x0, x5, 0, 1
      ret
  Machine code calls the thunk, and every variable
  that records a trampoline records its thunk.
- The enilopmarts reset the Domain Return Stack to the base the VM captured on entry, dropping the records of the
  exits that never returned.
"
Class {
	#name : 'VMRISCV64JITDomainExitTest',
	#superclass : 'VMSimpleStackBasedCogitAbstractTest',
	#category : 'VMMakerTests-JitTests',
	#package : 'VMMakerTests',
	#tag : 'JitTests'
}

{ #category : 'tests' }
VMRISCV64JITDomainExitTest class >> wordSizeParameters [

	^ ParametrizedTestMatrix new
		addCase: { #ISA -> #'riscv64' . #wordSize -> 8 . #jitDomain -> true };
		yourself
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> addressesNamed: aString [

	"The addresses the run-time table records for aString: the gate, then the thunk"

	| table |
	table := cogit instVarNamed: 'trampolineAddresses'.
	^ ((0 to: (cogit instVarNamed: 'trampolineTableIndex') - 1 by: 2)
		select: [ :i | (table at: i) = aString ])
		collect: [ :i | table at: i + 1 ]
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> assertPrimitiveGateStopsOnSlot: slot [

	"The primitive gate stops on slot, forged by machine code: it calls nothing and does not return"

	| function thunk startToEnd |
	function := self fakeCFunction: [ cogit MoveCq: 42 R: ReceiverResultReg ].
	cogit jitDomainPrimitiveSlotFor: function.
	cogit allocateOpcodes: 20 bytecodes: 0.
	thunk := cogit genPrimitiveCallGate.
	cogit methodZone manageFrom: cogit fixedCodeCursor to: memory getMemoryMap codeZoneEnd.
	startToEnd := self callThunk: thunk.
	machineSimulator
		temporaryRegisterValue: slot;
		receiverRegisterValue: 0;
		classRegisterValue: 0.

	"Unicorn reports the ebreak as an invalid instruction"
	self should: [ self runFromTo: startToEnd ] raise: UnicornError.

	self assert: (self wordAt: machineSimulator instructionPointerRegisterValue) equals: 16r00100073.
	self assert: machineSimulator receiverRegisterValue equals: 0.
	self assert: machineSimulator classRegisterValue equals: 0
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> base [

	^ self domainReturnStackBase
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> callThunk: thunk [

	"Compile a call site: CallRT: thunk; ClassReg := 7. Answer its start and end addresses."

	| start end |
	start := self compile: [
		cogit CallRT: thunk.
		cogit MoveCq: 7 R: ClassReg.
		end := cogit Label ] bytecodes: 10.
	^ start -> end address
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> fakeCFunction: aBlock [

	"Machine code standing for a C function: aBlock's code, then ret. Answer its address."

	^ self gateWith: [
		cogit zeroOpcodeIndex.
		aBlock value.
		cogit RetN: 0 ]
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> gateWith: aBlock [

	"Generate a gate whose code aBlock generates, as generateTrampolines does, and answer its address"

	| gate |
	cogit allocateOpcodes: 20 bytecodes: 0.
	aBlock value.
	gate := cogit methodZoneBase.
	cogit outputInstructionsForGeneratedRuntimeAt: gate.
	^ gate
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> generateRunTime [

	cogit generateTrampolines.
	cogit methodZone manageFrom: cogit methodZoneBase to: memory getMemoryMap codeZoneEnd
]

{ #category : 'accessing' }
VMRISCV64JITDomainExitTest >> hart [

	^ machineSimulator jitDomain
]

{ #category : 'running' }
VMRISCV64JITDomainExitTest >> jitCompilerClass [

	^ StackToRegisterMappingCogit
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> runFromTo: startToEnd [

	machineSimulator startAt: startToEnd key until: startToEnd value timeout: 0 count: 1000
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> should: aBlock faultWith: aSubcode [

	| fault |
	fault := nil.
	aBlock on: JITDomainFault do: [ :e | fault := e ].
	self assert: fault notNil description: 'no domain CFI fault'.
	self assert: fault subcode equals: aSubcode
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> signed: aValue bits: aNumber [

	^ aValue >= (1 << (aNumber - 1))
		ifTrue: [ aValue - (1 << aNumber) ]
		ifFalse: [ aValue ]
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> targetOfThunk: thunk [

	"Decode the gate address of auipc/addi x5"

	^ thunk
		+ ((self signed: (self wordAt: thunk) >> 12 bits: 20) << 12)
		+ (self signed: (self wordAt: thunk + 4) >> 20 bits: 12)
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testCCallGatePassesArgumentsAndResult [

	"A gate that calls a fixed C routine (ceCheckProfileTick, mcprimHashMultiply) leaves the C argument and
	 result registers alone"

	| function thunk start end |
	function := self fakeCFunction: [
		cogit AddCq: 1 R: cogit backEnd cResultRegister ].
	cogit allocateOpcodes: 20 bytecodes: 0.
	thunk := cogit genCCallGateFor: function called: 'testCCall'.
	cogit methodZone manageFrom: cogit fixedCodeCursor to: memory getMemoryMap codeZoneEnd.
	start := self compile: [
		cogit MoveCq: 41 R: cogit backEnd cResultRegister.
		cogit CallRT: thunk.
		cogit MoveR: cogit backEnd cResultRegister R: ReceiverResultReg.
		end := cogit Label ] bytecodes: 10.

	self runFromTo: start -> end address.

	self assert: machineSimulator receiverRegisterValue equals: 42.
	self assert: self hart drsDepth equals: 0.
	self assert: self hart dsp equals: self base
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testCapturedBaseIsTheDomainReturnStackPointer [

	cogit genJitDomainUdspRoutines.
	self hart dsp: self base - 32.
	cogit jitDomainCaptureUdspBase.
	self assert: cogit getJitDomainUdspBase equals: self base - 32.

	self hart dsp: self base - 56.
	cogit jitDomainResetUdsp.
	self assert: self hart dsp equals: self base - 32
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testEnilopmartsResetTheDomainReturnStack [

	"Enilopmarts start by dropping the records left above the base"

	| startToEnd |
	startToEnd := self compileWithEnd: [ cogit genResetUdspToBase: TempReg ].
	self hart dsp: self base - 24.
	self runFromTo: startToEnd.
	self assert: self hart dsp equals: self base
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testGateReturnsThroughItsThunk [

	| gate thunk startToEnd |
	gate := self gateWith: [
		cogit zeroOpcodeIndexForGate.
		cogit MoveCq: 42 R: ReceiverResultReg.
		cogit genGateReturn ].
	thunk := cogit gateEntryFor: gate called: 'testGate'.
	cogit methodZone manageFrom: cogit fixedCodeCursor to: memory getMemoryMap codeZoneEnd.
	startToEnd := self callThunk: thunk.

	self runFromTo: startToEnd.

	self assert: machineSimulator receiverRegisterValue equals: 42.
	self assert: machineSimulator classRegisterValue equals: 7.
	self assert: self hart curdom equals: 0.
	self assert: self hart drsDepth equals: 0.
	self assert: self hart dsp equals: self base
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testPrimitiveGateCallsTheFunctionInItsSlot [

	"The primitive gate calls the function in the slot machine code passes, not the one in
	 primitiveFunctionPointer, which it sets, and returns to the call site through its thunk"

	| function forged thunk startToEnd |
	function := self fakeCFunction: [ cogit MoveCq: 42 R: ReceiverResultReg ].
	forged := self fakeCFunction: [ cogit MoveCq: 13 R: ReceiverResultReg ].
	cogit allocateOpcodes: 20 bytecodes: 0.
	thunk := cogit genPrimitiveCallGate.
	cogit methodZone manageFrom: cogit fixedCodeCursor to: memory getMemoryMap codeZoneEnd.
	interpreter primitiveFunctionPointer: forged.
	startToEnd := self callThunk: thunk.
	machineSimulator temporaryRegisterValue: (cogit jitDomainPrimitiveSlotFor: function).

	self runFromTo: startToEnd.

	self assert: machineSimulator receiverRegisterValue equals: 42.
	self assert: machineSimulator classRegisterValue equals: 7.
	self assert: interpreter primitiveFunctionPointer equals: function.
	self assert: self hart curdom equals: 0.
	self assert: self hart drsDepth equals: 0.
	self assert: self hart dsp equals: self base.
	self assert: (self hart events detect: [ :e | e first = #domcall ]) last equals: 2
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testPrimitiveGateStopsOnASlotOutOfTheTable [

	self assertPrimitiveGateStopsOnSlot: cogit jitDomainPrimitiveSlots
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testPrimitiveGateStopsOnAnEmptySlot [

	self assertPrimitiveGateStopsOnSlot: cogit jitDomainPrimitiveSlots - 1
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testPrimitiveSlotsAreSharedAndReused [

	"A function keeps its slot, and the slot of a forgotten function goes to the next new one"

	| first second |
	first := cogit jitDomainPrimitiveSlotFor: 16r1000.
	self assert: (cogit jitDomainPrimitiveSlotFor: 16r1000) equals: first.
	second := cogit jitDomainPrimitiveSlotFor: 16r2000.
	self deny: second equals: first.
	cogit jitDomainForgetPrimitiveFunction: 16r1000.
	self assert: (cogit jitDomainPrimitiveSlotFor: 16r3000) equals: first.
	self assert: (cogit jitDomainPrimitiveSlotFor: 16r2000) equals: second
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testRunTimeLayout [

	"Gates below the fixed code area, their thunks and the helpers in it, the method zone after it"

	| fixedStart |
	self generateRunTime.
	fixedStart := cogit jitDomainFixedCodeStart.
	self assert: fixedStart \\ 4096 equals: 0.
	self assert: (cogit fixedCodeCursor) equals: cogit methodZoneBase.

	#( 'ceSend0Args' 'ceSuperSendNArgs' 'ceMethodAbort1Args' 'cePICAbort2Args' 'cePICMissNArgs' 'ceStoreCheckTrampoline'
	   'ceCheckForInterruptsTrampoline' 'ceReturnToInterpreterTrampoline' 'ceBaseFrameReturnTrampoline'
	   'ceCallPrimitiveTrampoline' 'ceCheckProfileTickTrampoline' 'ceMcprimHashMultiplyTrampoline' ) do: [ :name |
		| addresses |
		addresses := self addressesNamed: name.
		self assert: addresses size equals: 2.
		self assert: addresses first < fixedStart.
		self assert: (addresses second between: fixedStart and: cogit methodZoneBase - 1) ].

	#( 'ceEnterCogCodePopReceiverReg' 'ceCallPIC0Args' 'cePrimReturnEnterCogCode' 'ceDereferenceSelectorIndex' ) do: [ :name |
		self assert: (self addressesNamed: name) size equals: 1.
		self assert: (self addressesNamed: name) first < fixedStart ].

	#( 'ceSmallMethodContext' 'ceLargeFullBlockContext' 'ceStoreCheckContextReceiver' ) do: [ :name |
		self assert: (self addressesNamed: name) size equals: 1.
		self assert: ((self addressesNamed: name) first between: fixedStart and: cogit methodZoneBase - 1) ]
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testSendsAreLinkedToThunks [

	"What call sites, relinking and isSendReturnPC: see: the send variables hold thunks, within [firstSend, lastSend]"

	| sends |
	self generateRunTime.
	sends := (0 to: 3) collect: [ :n | (cogit instVarNamed: 'ordinarySendTrampolines') at: n ].
	self assert: sends equals: ((0 to: 3) collect: [ :n | (self addressesNamed: 'ceSend' , (n = 3 ifTrue: [ 'N' ] ifFalse: [ n printString ]) , 'Args') second ]).
	self assert: (cogit instVarNamed: 'firstSend') equals: sends first.
	self assert: ((cogit instVarNamed: 'superSendTrampolines') at: 3) equals: (cogit instVarNamed: 'lastSend').
	self assert: (cogit instVarNamed: 'lastSend') < cogit methodZoneBase.
	self assert: (cogit instVarNamed: 'firstSend') >= cogit jitDomainFixedCodeStart
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testThunkEntersItsGateWithTheCallSiteReturnAddress [

	| thunk gate startToEnd |
	self generateRunTime.
	thunk := (self addressesNamed: 'ceSend1Args') second.
	gate := (self addressesNamed: 'ceSend1Args') first.
	startToEnd := self callThunk: thunk.

	machineSimulator startAt: startToEnd key until: gate + 4 timeout: 0 count: 100.

	self assert: machineSimulator instructionPointerRegisterValue equals: gate + 4.
	self assert: machineSimulator linkRegisterValue equals: startToEnd key + 8.
	self assert: self hart curdom equals: 0.
	self assert: self hart drsDepth equals: 1.
	self assert: self hart events last equals: { #domcall. thunk + 8. gate. 0. 0. 1 }
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testThunkToAPadWithAnotherLabelFaults [

	| gate thunk startToEnd |
	gate := self gateWith: [
		cogit zeroOpcodeIndex.
		cogit backend genDomainLandingPad: 0 label: 2.
		cogit genGateReturn ].
	thunk := cogit gateEntryFor: gate called: 'testGate'.
	cogit methodZone manageFrom: cogit fixedCodeCursor to: memory getMemoryMap codeZoneEnd.
	startToEnd := self callThunk: thunk.

	self should: [ self runFromTo: startToEnd ] faultWith: #LPAD
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testThunkToCodeWithoutAPadFaults [

	| gate thunk startToEnd |
	gate := self gateWith: [
		cogit zeroOpcodeIndex.
		cogit MoveCq: 42 R: ReceiverResultReg.
		cogit genGateReturn ].
	thunk := cogit gateEntryFor: gate called: 'testGate'.
	cogit methodZone manageFrom: cogit fixedCodeCursor to: memory getMemoryMap codeZoneEnd.
	startToEnd := self callThunk: thunk.

	self should: [ self runFromTo: startToEnd ] faultWith: #LPAD
]

{ #category : 'tests' }
VMRISCV64JITDomainExitTest >> testThunksCallTheirGatesAtTheirPads [

	"Every gate starts with domlpad 0, label, and its thunk is auipc/addi x5, gate; domcall x0, x5, 0, label; ret.
	 The label is 2 for the primitive gates, 1 for the others."

	| ret checked |
	self generateRunTime.
	ret := 16r00008067.
	checked := 0.
	((cogit instVarNamed: 'trampolineAddresses') object first: (cogit instVarNamed: 'trampolineTableIndex'))
		pairsDo: [ :name :address |
			| addresses label |
			addresses := self addressesNamed: name.
			(addresses size = 2 and: [ address = addresses second ]) ifTrue: [
				label := (name beginsWith: 'ceCallPrimitive') ifTrue: [ 2 ] ifFalse: [ 1 ].
				self assert: (self targetOfThunk: address) equals: addresses first.
				self assert: (self wordAt: address + 8) equals: (cogit backend domainCallTo: 5 domain: 0 label: label).
				self assert: (self wordAt: address + 12) equals: ret.
				self assert: (self wordAt: addresses first) equals: (cogit backend domainLandingPad: 0 label: label).
				checked := checked + 1 ] ].
	self assert: checked > 40
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> compileWithEnd: aBlock [

	| start end |
	start := self compile: [ aBlock value. end := cogit Label ] bytecodes: 10.
	^ start -> end address
]

{ #category : 'helpers' }
VMRISCV64JITDomainExitTest >> wordAt: anAddress [

	^ (machineSimulator memoryAt: anAddress readNext: 4) unsignedLongAt: 1 bigEndian: false
]
