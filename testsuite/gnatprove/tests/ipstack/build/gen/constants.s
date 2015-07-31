	.globl _constants_E
	.data
	.align 1
_constants_E:
	.space 2
	.globl _constants__c00GP613__nameX
	.const
	.align 4
_constants__c00GP613__nameX:
	.ascii "Address_Size"
	.space 4
	.globl _constants__c00GP613__valX
	.align 2
_constants__c00GP613__valX:
	.long	64
	.globl _constants__c01GP687__nameX
	.align 4
_constants__c01GP687__nameX:
	.ascii "Default_Bit_Order"
	.globl _constants__c01GP687__valX
	.align 2
_constants__c01GP687__valX:
	.long	1
	.globl _constants__c02GP792__nameX
	.align 4
_constants__c02GP792__nameX:
	.ascii "Network_Bit_Order"
	.globl _constants__c02GP792__valX
	.align 2
_constants__c02GP792__valX:
	.space 4
	.text
	.align 1,0x90
	.globl _constants__c00
_constants__c00:
LFB2:
	pushq	%rbp
LCFI0:
	movq	%rsp, %rbp
LCFI1:
	leaq	_constants__c00GP613__valX(%rip), %rax
	movq	%rax, -8(%rbp)
# 9 "/Users/moy/spark2014/testsuite/gnatprove/tests/ipstack/src/bldtools/constants.adb" 1
	
->CND:$0:Address_Size:$64:Address_Size
# 0 "" 2
	popq	%rbp
LCFI2:
	ret
LFE2:
	.align 1,0x90
	.globl _constants__c01
_constants__c01:
LFB3:
	pushq	%rbp
LCFI3:
	movq	%rsp, %rbp
LCFI4:
	leaq	_constants__c01GP687__valX(%rip), %rax
	movq	%rax, -8(%rbp)
# 9 "/Users/moy/spark2014/testsuite/gnatprove/tests/ipstack/src/bldtools/constants.adb" 1
	
->CND:$0:Default_Bit_Order:$1:Default_Bit_Order
# 0 "" 2
	popq	%rbp
LCFI5:
	ret
LFE3:
	.align 1,0x90
	.globl _constants__c02
_constants__c02:
LFB4:
	pushq	%rbp
LCFI6:
	movq	%rsp, %rbp
LCFI7:
	leaq	_constants__c02GP792__valX(%rip), %rax
	movq	%rax, -8(%rbp)
# 9 "/Users/moy/spark2014/testsuite/gnatprove/tests/ipstack/src/bldtools/constants.adb" 1
	
->CND:$0:Network_Bit_Order:$0:Network_Bit_Order
# 0 "" 2
	popq	%rbp
LCFI8:
	ret
LFE4:
	.align 1,0x90
	.globl _constants___elabb
_constants___elabb:
LFB0:
	pushq	%rbp
LCFI9:
	movq	%rsp, %rbp
LCFI10:
	popq	%rbp
LCFI11:
	ret
LFE0:
	.section __TEXT,__eh_frame,coalesced,no_toc+strip_static_syms+live_support
EH_frame1:
	.set L$set$0,LECIE1-LSCIE1
	.long L$set$0
LSCIE1:
	.long	0
	.byte	0x1
	.ascii "zR\0"
	.byte	0x1
	.byte	0x78
	.byte	0x10
	.byte	0x1
	.byte	0x10
	.byte	0xc
	.byte	0x7
	.byte	0x8
	.byte	0x90
	.byte	0x1
	.align 3
LECIE1:
LSFDE1:
	.set L$set$1,LEFDE1-LASFDE1
	.long L$set$1
LASFDE1:
	.long	LASFDE1-EH_frame1
	.quad	LFB2-.
	.set L$set$2,LFE2-LFB2
	.quad L$set$2
	.byte	0
	.byte	0x4
	.set L$set$3,LCFI0-LFB2
	.long L$set$3
	.byte	0xe
	.byte	0x10
	.byte	0x86
	.byte	0x2
	.byte	0x4
	.set L$set$4,LCFI1-LCFI0
	.long L$set$4
	.byte	0xd
	.byte	0x6
	.byte	0x4
	.set L$set$5,LCFI2-LCFI1
	.long L$set$5
	.byte	0xc
	.byte	0x7
	.byte	0x8
	.align 3
LEFDE1:
LSFDE3:
	.set L$set$6,LEFDE3-LASFDE3
	.long L$set$6
LASFDE3:
	.long	LASFDE3-EH_frame1
	.quad	LFB3-.
	.set L$set$7,LFE3-LFB3
	.quad L$set$7
	.byte	0
	.byte	0x4
	.set L$set$8,LCFI3-LFB3
	.long L$set$8
	.byte	0xe
	.byte	0x10
	.byte	0x86
	.byte	0x2
	.byte	0x4
	.set L$set$9,LCFI4-LCFI3
	.long L$set$9
	.byte	0xd
	.byte	0x6
	.byte	0x4
	.set L$set$10,LCFI5-LCFI4
	.long L$set$10
	.byte	0xc
	.byte	0x7
	.byte	0x8
	.align 3
LEFDE3:
LSFDE5:
	.set L$set$11,LEFDE5-LASFDE5
	.long L$set$11
LASFDE5:
	.long	LASFDE5-EH_frame1
	.quad	LFB4-.
	.set L$set$12,LFE4-LFB4
	.quad L$set$12
	.byte	0
	.byte	0x4
	.set L$set$13,LCFI6-LFB4
	.long L$set$13
	.byte	0xe
	.byte	0x10
	.byte	0x86
	.byte	0x2
	.byte	0x4
	.set L$set$14,LCFI7-LCFI6
	.long L$set$14
	.byte	0xd
	.byte	0x6
	.byte	0x4
	.set L$set$15,LCFI8-LCFI7
	.long L$set$15
	.byte	0xc
	.byte	0x7
	.byte	0x8
	.align 3
LEFDE5:
LSFDE7:
	.set L$set$16,LEFDE7-LASFDE7
	.long L$set$16
LASFDE7:
	.long	LASFDE7-EH_frame1
	.quad	LFB0-.
	.set L$set$17,LFE0-LFB0
	.quad L$set$17
	.byte	0
	.byte	0x4
	.set L$set$18,LCFI9-LFB0
	.long L$set$18
	.byte	0xe
	.byte	0x10
	.byte	0x86
	.byte	0x2
	.byte	0x4
	.set L$set$19,LCFI10-LCFI9
	.long L$set$19
	.byte	0xd
	.byte	0x6
	.byte	0x4
	.set L$set$20,LCFI11-LCFI10
	.long L$set$20
	.byte	0xc
	.byte	0x7
	.byte	0x8
	.align 3
LEFDE7:
	.subsections_via_symbols
