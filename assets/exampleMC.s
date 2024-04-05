# the entry for the RECOGNIZER FUNCTION is NOT HERE, read on
# trap state return
add rsp, 0x8
mov rax, 0x0
ret
# check whether the final state is accepting
add rsp, 0x8
mov rax, 0x241fb0 # JIT address of the function that checks whether the final state is contained in the set of accepting states
jmp rax # jump to the function, think of this as a call that doesn't jump back here, but one level up
# actual start of the recognizer function
sub rsp, 0x8
mov rax, rsi
# start of state machine code
mov cl, byte ptr [rax]
add rax, 0x1
cmp cl, 0x1
jc 0xb
cmp cl, 0x77
jbe 0x2b
cmp cl, 0x78
jz 0x5a
cmp cl, 0x79
jc 0xb
cmp cl, 0xff
jbe 0x14
cmp cl, 0x0
mov rsi, 0x0
jz 0xffffffffffffffb7
jmp 0xffffffffffffffa9
mov cl, byte ptr [rax]
add rax, 0x1
cmp cl, 0x61
jc 0xb
cmp cl, 0x63
jbe 0x78
cmp cl, 0x66
jc 0xb
cmp cl, 0x69
jbe 0x9d
cmp cl, 0x77
jz 0xffffffffffffffdb
cmp cl, 0x0
mov rsi, 0x1
jz 0xffffffffffffff82
jmp 0xffffffffffffff74
mov cl, byte ptr [rax]
add rax, 0x1
cmp cl, 0x61
jc 0xb
cmp cl, 0x63
jbe 0x40
cmp cl, 0x66
jc 0xb
cmp cl, 0x69
jbe 0x65
cmp cl, 0x77
jz 0xffffffffffffffa3
cmp cl, 0x79
jz 0x72
cmp cl, 0x7a
jz 0x69
cmp cl, 0x0
mov rsi, 0x2
jz 0xffffffffffffff38
jmp 0xffffffffffffff26
mov cl, byte ptr [rax]
add rax, 0x1
cmp cl, 0x61
jc 0x7
cmp cl, 0x63
jbe 0xfffffffffffffff2
cmp cl, 0x66
jc 0xb
cmp cl, 0x69
jbe 0x1b
cmp cl, 0x0
mov rsi, 0x3
jz 0xffffffffffffff05
jmp 0xfffffffffffffef3
mov cl, byte ptr [rax]
add rax, 0x1
cmp cl, 0x0
mov rsi, 0x4
jz 0xfffffffffffffeea
jmp 0xfffffffffffffed8
mov cl, byte ptr [rax]
add rax, 0x1
cmp cl, 0x0
mov rsi, 0x5
jz 0xfffffffffffffecf
jmp 0xfffffffffffffebd
