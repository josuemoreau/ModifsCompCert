# File generated by CompCert 3.11
# Command line: test_stage/test.b -db -S -o test_stage/test.s
	.text
	.align	16
	.globl $96
$96:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	leaq	1(%rdi), %rax
	leaq	0(%rax,%rsi,1), %rax
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	$96, @function
	.size	$96, . - $96
	.text
	.align	16
	.globl $97
$97:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	movq	$1, %rdi
	movq	$3, %rsi
	call	$96
	xorl	%eax, %eax
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	$97, @function
	.size	$97, . - $97
