create_clock -name virtual_clk -period @PERIOD_PS@
set_input_delay 0 -clock virtual_clk [all_inputs]
set_output_delay 0 -clock virtual_clk [all_outputs]
