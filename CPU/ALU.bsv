   function Action fa_ALU_AOM (ALU_Inputs inputs);
      action
      CPU_State next_state = CPU_EXEC2;

      // Single-cycle ALU outputs and selects
      Vector #(7, ALU_Data_Out) alu_outputs = repeat (alu_data_out_base);
      Vector #(7, Bool) sel_outputs = repeat (False);
`ifdef ISA_M
      Vector #(11, ALU_Ctrl_Out) alu_controls = repeat (CONTROL_STRAIGHT);
      Vector #(10, Bool) sel_controls = repeat (False);
`else
      Vector #(10, ALU_Ctrl_Out) alu_controls = repeat (CONTROL_STRAIGHT);
      Vector #(9, Bool) sel_controls = repeat (False);
`endif

      // Select bit positions for alu datapath outputs
      Integer branch_op_bitpos = 0;
      Integer jal_op_bitpos = 1;
      Integer jalr_op_bitpos = 2;
      Integer op_op_imm_op_bitpos = 3;
      Integer lui_op_bitpos = 4;
      Integer auipc_op_bitpos = 5;
      Integer system_op_bitpos = 6;

      // Select bit positions for alu control outputs
      Integer branch_ctrl_bitpos = 0;
      Integer jal_ctrl_bitpos = 1;
      Integer jalr_ctrl_bitpos = 2;
      Integer op_op_imm_ctrl_bitpos = 3;
      Integer ui_ctrl_bitpos = 4;
      Integer misc_mem_ctrl_bitpos = 5;
      Integer system_ctrl_bitpos = 6;
      Integer ldst_ctrl_bitpos  = 7;
      Integer shift_ctrl_bitpos = 8;
`ifdef ISA_M
      Integer mul_ctrl_bitpos   = 9;
      Integer illegal_ctrl_bitpos = 10;
`else
      Integer illegal_ctrl_bitpos = 9;
`endif

      let funct3 = instr_funct3 (inputs.instr);

      let alu_branch                   = fv_BRANCH (inputs);
      sel_outputs [branch_op_bitpos]   = (inputs.ucontrol.opcode.is_op_BRANCH);
      sel_controls[branch_ctrl_bitpos] = sel_outputs [branch_op_bitpos];
      alu_controls [branch_ctrl_bitpos]= tpl_1 (alu_branch);
      alu_outputs [branch_op_bitpos]   = tpl_2 (alu_branch);

      let alu_jal                      = fv_JAL (inputs);
      sel_outputs [jal_op_bitpos]      = (inputs.ucontrol.opcode.is_op_JAL);
      sel_controls[jal_ctrl_bitpos]    = (inputs.ucontrol.opcode.is_op_JAL);
      alu_controls [jal_ctrl_bitpos]   = tpl_1 (alu_jal);
      alu_outputs [jal_op_bitpos]      = tpl_2 (alu_jal);

      let alu_jalr                     = fv_JALR (inputs);
      sel_outputs [jalr_op_bitpos]     = (inputs.ucontrol.opcode.is_op_JALR);
      sel_controls[jalr_ctrl_bitpos]   = (inputs.ucontrol.opcode.is_op_JALR);
      alu_controls [jalr_ctrl_bitpos]  = tpl_1 (alu_jalr);
      alu_outputs [jalr_op_bitpos]     = tpl_2 (alu_jalr);

      sel_controls[ui_ctrl_bitpos]     = (   (inputs.ucontrol.opcode.is_op_LUI) 
                                          || (inputs.ucontrol.opcode.is_op_AUIPC));
      alu_controls [ui_ctrl_bitpos]    = CONTROL_STRAIGHT;
      sel_outputs [lui_op_bitpos]      = (inputs.ucontrol.opcode.is_op_LUI);
      alu_outputs [lui_op_bitpos]      = fv_LUI (inputs);
      sel_outputs [auipc_op_bitpos]    = (inputs.ucontrol.opcode.is_op_AUIPC);
      alu_outputs [auipc_op_bitpos]    = fv_AUIPC (inputs);

      sel_controls[misc_mem_ctrl_bitpos] = (inputs.ucontrol.opcode.is_op_MISC_MEM);
      alu_controls[misc_mem_ctrl_bitpos] = fv_MISC_MEM_control (inputs);

      let alu_system                   = fv_SYSTEM (inputs);
      sel_outputs [system_op_bitpos]   = (inputs.ucontrol.opcode.is_op_SYSTEM);
      sel_controls[system_ctrl_bitpos] = (inputs.ucontrol.opcode.is_op_SYSTEM);
      alu_controls[system_ctrl_bitpos] = tpl_1 (alu_system);
      alu_outputs [system_op_bitpos]   = tpl_2 (alu_system);

      let alu_imm                      = fv_OP_and_OP_IMM (inputs);
      sel_outputs [op_op_imm_op_bitpos]= (
            (   (inputs.ucontrol.opcode.is_op_OP_IMM)
             || (   inputs.ucontrol.opcode.is_op_OP
`ifdef ISA_M
                 && !inputs.ucontrol.f7.is_f7_MUL_DIV_REM
`endif
                )
            )
         && (    !(inputs.ucontrol.f3.is_f3_SLL)
              && !(inputs.ucontrol.f3.is_f3_SRx)
            ));

      sel_controls[op_op_imm_ctrl_bitpos] = sel_outputs[op_op_imm_op_bitpos];
      alu_controls[op_op_imm_ctrl_bitpos] = tpl_1 (alu_imm);
      alu_outputs[op_op_imm_op_bitpos] = tpl_2 (alu_imm);

      alu_controls [illegal_ctrl_bitpos] = CONTROL_TRAP;
      sel_controls [illegal_ctrl_bitpos] = !(fold (\|| , sel_controls));

      ALU_Data_Out alu_data_out = unpack (fv_and_or_mux (sel_outputs, map (pack, alu_outputs)));

      // Multi-cycle operations
      sel_controls [ldst_ctrl_bitpos] = (   (inputs.ucontrol.opcode.is_op_LOAD)
                                         || (inputs.ucontrol.opcode.is_op_STORE));
      alu_controls [ldst_ctrl_bitpos]  = fv_LDST_control (inputs);

      sel_controls [shift_ctrl_bitpos] =  (   (   (inputs.ucontrol.opcode.is_op_OP_IMM)
                                               || (    inputs.ucontrol.opcode.is_op_OP
`ifdef ISA_M
                                                   && !inputs.ucontrol.f7.is_f7_MUL_DIV_REM
`endif
                                                  )
                                              )
                                           && (   (inputs.ucontrol.f3.is_f3_SLL)
                                               || (inputs.ucontrol.f3.is_f3_SRx)));
      alu_controls [shift_ctrl_bitpos] = fv_SHIFT_control (inputs);

`ifdef ISA_M
      sel_controls [mul_ctrl_bitpos]   = (   inputs.ucontrol.opcode.is_op_OP
                                          && inputs.ucontrol.f7.is_f7_MUL_DIV_REM);
      alu_controls [mul_ctrl_bitpos]   = CONTROL_STRAIGHT;
`endif


`ifdef ISA_M
      // OP 'M' ops MUL/ MULH/ MULHSU/ MULHU/ DIV/ DIVU/ REM/ REMU
      if (   inputs.ucontrol.opcode.is_op_OP
          && inputs.ucontrol.f7.is_f7_MUL_DIV_REM) begin
         // Dispatch to MBox
         fa_MUL (inputs, mbox);
         next_state = CPU_M_COMPLETION;
      end
`endif

`ifdef SHIFT_SERIAL
      // OP_IMM and OP (shifts)
      if (   (   (inputs.ucontrol.opcode.is_op_OP_IMM)
              || (inputs.ucontrol.opcode.is_op_OP))
          && (   (inputs.ucontrol.f3.is_f3_SLL)
              || (inputs.ucontrol.f3.is_f3_SRx))
          && (   (instr_I_imm12 (inputs.instr))[5] == 0) // trap condition
         ) begin
         // Dispatch to SBox
         fa_OP_and_OP_IMM_shifts (inputs, sbox);
         next_state = CPU_SH_COMPLETION;
      end
`endif

      // XXX Does not handle FP loads/stores
      if ((    (inputs.ucontrol.opcode.is_op_LOAD)
            || (inputs.ucontrol.opcode.is_op_STORE)
          ) && (inputs.ucontrol.f3.is_LDST_legal)) begin
         // Dispatch to near mem
         fa_LD_ST (inputs, near_mem.dmem);
         next_state = inputs.ucontrol.opcode.is_op_LOAD ? CPU_LD_COMPLETION
                                                        : CPU_SH_COMPLETION;
      end

      // MISC MEM dispatch
      if (   (inputs.ucontrol.opcode.is_op_MISC_MEM) 
          && (alu_controls[misc_mem_ctrl_bitpos] != CONTROL_TRAP)) begin
         fa_MISC_MEM (alu_controls [misc_mem_ctrl_bitpos], near_mem.dmem);
         next_state = (alu_controls[misc_mem_ctrl_bitpos] == CONTROL_FENCE) ? CPU_FENCE_COMPLETION
                                                                            : CPU_FENCE_I_COMPLETION;
      end

      ALU_Ctrl_Out alu_ctrl_out  = unpack (fv_and_or_mux (sel_controls, map (pack, alu_controls)));

      rg_state <= next_state;
      rg_alu_data_out <= alu_data_out;
      rg_alu_ctrl_out <= alu_ctrl_out;
      endaction
   endfunction
