`timescale 1ns/1ns

module async_fifo_tb;
	parameter data_width = 8;
	
	logic [data_width-1:0] data_in;
	logic w_en, r_en, w_clk, r_clk,wrst_n,rrst_n;
	logic full,empty;
	logic [data_width-1:0] data_out;

	initial begin
		w_clk = 0;
		forever #5 w_clk = ~w_clk;
	end
	
	initial begin
		r_clk = 0;
		forever #10 r_clk = ~r_clk;
	end

	top DUT (
		.data_in(data_in),
		.w_en(w_en),
		.r_en(r_en),
		.w_clk(w_clk),
		.r_clk(r_clk),
		.wrst_n(wrst_n),
		.rrst_n(rrst_n),
		.full(full),
		.empty(empty),
		.data_out(data_out)
	);
	
	initial begin
		$display("*** Simulation Starts  ***");
		wrst_n = 0;
		w_en = 0;
		@(negedge w_clk);
		wrst_n = 1;
		data_in = 8'hAB;
		w_en = 1;
		@(negedge w_clk);
		w_en = 0;
		@(negedge w_clk);
		data_in = 8'hCD;
		w_en = 1;
		@(negedge w_clk);
		w_en = 0;
		data_in = 8'd0;
	end
	
	initial begin
		rrst_n = 0;
		r_en = 0;
		@(negedge r_clk);
		rrst_n = 1;
		repeat(3) @(negedge r_clk);
		r_en = 1;
		@(negedge r_clk);
		$display("data_out : %H", data_out);
		r_en = 0;
		@(negedge r_clk);
		r_en = 1;
		@(negedge r_clk);
		$display("data_out : %H", data_out);
		r_en = 0;
		$stop;
	end

endmodule
