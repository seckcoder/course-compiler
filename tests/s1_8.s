	.globl _main
_main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp

	movq	$1, %rax
	cmpq	$0, %rax
	je else740
	movq	$1, %rbx
	jmp if_end741
else740:
	movq	$0, %rbx
if_end741:
	cmpq	$0, %rbx
	je else742
	movq	$42, %rbx
	jmp if_end743
else742:
	movq	$777, %rbx
if_end743:
	movq	%rbx, %rax

	addq	$16, %rsp
	popq	%rbp
	retq

