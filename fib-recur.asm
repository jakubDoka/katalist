    global main

    section .text
main:
    push r15
    push rbp
    mov rbp, rsp
    mov rdi, 0xa
    call L1
    mov r15, rax
    mov rax, r15
    jmp L2
L2:
    mov rsp, rbp
    pop rbp
    pop r15
    ret
L1:
    push r13
    push r14
    push r15
    push rbp
    mov rbp, rsp
    mov r15, rdi
    cmp r15, 0x2
    setl r14b
    movzx r14, r14b
    cmp r14, 0x0
    je L3
    mov rax, rdi
    jmp L4
    L3:
    mov r15, rdi
    dec r15
    push rdi
    mov rdi, r15
    call L1
    pop rdi
    mov r15, rax
    mov r13, rdi
    sub r13, 0x2
    push rdi
    mov rdi, r13
    call L1
    pop rdi
    mov r13, rax
    add r15, r13
    mov rax, r15
    jmp L4
L4:
    mov rsp, rbp
    pop rbp
    pop r15
    pop r14
    pop r13
    ret
