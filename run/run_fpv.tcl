
set_fml_appmode FPV 
set design top

read_file -top top -format sverilog -sva -vcs {-lca -f ../RTL/filelist}

create_clock w_clk -period 100
create_clock r_clk -period 100

# We are specifying the clocks are asynchronous to each other
set_clock_groups -asynchronous -group {w_clk} -group {r_clk}


# Write domain reset (active low)
create_reset wrst_n -sense low

# Read domain reset (active low)  
create_reset rrst_n -sense low

#set_input_constraint w_en {0 1}
#set_input_constraint r_en {0 1}

sim_run -stable
sim_save_reset



