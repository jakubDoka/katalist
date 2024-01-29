    global main

    section .text
main:
    push rbx
    push r12
    push r13
    push r14
    push r15
    push rbp
    mov rbp, rsp
    mov r15, 0x6
    mov rdi, 0x4
    call fn_1
    mov r14, rax
    mov r13, 0x5
    add r13, r14
    mov r14, r15
    add r14, r13
    mov r15, r14
    mov r13, 0x6
    mov rdi, 0x4
    call fn_1
    mov r12, rax
    mov r11, 0x5
    add r11, r12
    mov r12, r13
    add r12, r11
    mov r13, r12
    mov r11, 0x6
    mov rdi, 0x4
    call fn_1
    mov r10, rax
    mov r9, 0x5
    add r9, r10
    mov r10, r11
    add r10, r9
    mov r11, r10
    mov r9, 0x6
    mov rdi, 0x4
    call fn_1
    mov r8, rax
    mov rdi, 0x5
    add rdi, r8
    mov r8, r9
    add r8, rdi
    mov r9, r8
    mov rdi, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    mov rsi, rax
    mov rdx, 0x5
    add rdx, rsi
    mov rsi, rdi
    add rsi, rdx
    mov rdi, rsi
    mov rdx, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    mov rcx, rax
    mov rbx, 0x5
    add rbx, rcx
    mov rcx, rdx
    add rcx, rbx
    mov rdx, rcx
    mov rbx, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    push rbx
    mov rbx, rax
    push rcx
    mov rcx, 0x5
    add rcx, rbx
    pop rbx
    push rdx
    mov rdx, rbx
    add rdx, rcx
    pop rcx
    mov rbx, rdx
    push rsi
    mov rsi, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    push rdi
    mov rdi, rax
    push r8
    mov r8, 0x5
    add r8, rdi
    pop rdi
    push r9
    mov r9, rsi
    add r9, r8
    pop r8
    mov rsi, r9
    push r10
    mov r10, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    push r11
    mov r11, rax
    push r12
    mov r12, 0x5
    add r12, r11
    pop r11
    push r13
    mov r13, r10
    add r13, r12
    pop r12
    mov r10, r13
    push r14
    mov r14, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    push r15
    mov r15, rax
    push rbx
    mov rbx, 0x5
    add rbx, r15
    pop r15
    push rcx
    mov rcx, r14
    add rcx, rbx
    pop rbx
    mov r14, rcx
    push rdx
    mov rdx, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    push rsi
    mov rsi, rax
    push rdi
    mov rdi, 0x5
    add rdi, rsi
    pop rsi
    push r8
    mov r8, rdx
    add r8, rdi
    pop rdi
    mov rdx, r8
    push r9
    mov r9, 0x6
    push rdi
    mov rdi, 0x4
    call fn_1
    pop rdi
    push r10
    mov r10, rax
    push r11
    mov r11, 0x5
    add r11, r10
    pop r10
    push r12
    mov r12, r9
    add r12, r11
    pop r11
    mov r9, r12
    mov rax, r9
    pop r12
    pop r9
    pop r8
    pop rdx
    pop rcx
    pop r14
    pop r13
    pop r10
    pop r9
    pop rsi
    pop rdx
    jmp L2
L2:
    mov rsp, rbp
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
fn_1:
    push r14
    push r15
    push rbp
    mov rbp, rsp
    mov r15, rdi
    add r15, 0x4
    mov r14, rdi
    add r14, r15
    mov rax, r14
    jmp L3
L3:
    mov rsp, rbp
    pop rbp
    pop r15
    pop r14
    ret
