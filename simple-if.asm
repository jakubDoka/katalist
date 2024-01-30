    global main

    section .text
main:
    push r14
    push r15
    push rbp
    mov rbp, rsp
    call L1
    mov r15, rax
    cmp r15, 0x0
    je L2
    mov r14, 0x2
    jmp L3
    L2:
    mov r14, 0x3
    L3:
    mov rax, r14
    jmp L4
L4:
    mov rsp, rbp
    pop rbp
    pop r15
    pop r14
    ret
L1:
    push rbp
    mov rbp, rsp
    mov rax, 0x1
    jmp L5
L5:
    mov rsp, rbp
    pop rbp
    ret
