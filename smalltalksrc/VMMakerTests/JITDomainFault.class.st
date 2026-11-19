"
I am a domain CFI fault (cause 25) raised by the simulated JITDomain state of a RISC-V simulator.
My subcode is #LPAD for a domcall whose target is not a matching domlpad, #DRS for a bad Domain Return Stack
access, #GATE for a domcall that dgate forbids, #DSP for an access to udsp outside the VM domain (DOM0), or
#DSPRANGE for a udsp write outside [dsp, dspbase].
"
Class {
	#name : 'JITDomainFault',
	#superclass : 'Error',
	#instVars : [
		'subcode',
		'pc'
	],
	#category : 'VMMakerTests-Unicorn',
	#package : 'VMMakerTests',
	#tag : 'Unicorn'
}

{ #category : 'signalling' }
JITDomainFault class >> signal: aSubcode pc: anAddress [

	^ self new
		subcode: aSubcode;
		pc: anAddress;
		signal: 'Domain CFI fault ' , aSubcode , ' at 16r' , (anAddress printStringBase: 16)
]

{ #category : 'accessing' }
JITDomainFault >> pc [

	^ pc
]

{ #category : 'accessing' }
JITDomainFault >> pc: anAddress [

	pc := anAddress
]

{ #category : 'accessing' }
JITDomainFault >> subcode [

	^ subcode
]

{ #category : 'accessing' }
JITDomainFault >> subcode: aSymbol [

	subcode := aSymbol
]
