module read_ptr_handler #(parameter ptr_width = 6)(
    input logic rclk,
    input logic r_en,
    input logic rrst_n,
    input logic [ptr_width-1 :0] g_wptr_sync,
    output logic [ptr_width-1 :0] g_rptr,
    output logic [ptr_width-1 :0] b_rptr,
    output logic empty
);

logic [ptr_width-1 :0] b_rptr_next;
logic [ptr_width-1 :0] g_rptr_next;
logic rempty;

always_comb begin 
    if (b_rptr == 6'd54)
        b_rptr_next = 6'd9; // Wrap around
    else if (r_en && !empty)
        b_rptr_next = b_rptr + 1; // Increment
    else
        b_rptr_next = b_rptr; // hold     
end    

//assign b_rptr_next = (b_rptr == 6'b110110)? 6'b001001 : b_rptr + ((r_en & ~empty));
assign g_rptr_next = (b_rptr_next) ^ (b_rptr_next>>1);
assign rempty = (g_wptr_sync == g_rptr_next); //g_rptr_next - modified


always @(posedge rclk or negedge rrst_n) begin
    if (!rrst_n) begin
        b_rptr <= 6'd9;
        g_rptr <= 6'b001101; // gray code of 9
        empty <= 1'b1;
    end 
    else begin
        b_rptr <= b_rptr_next;
        g_rptr <= g_rptr_next;
        empty <= (g_wptr_sync == g_rptr_next);
    end
end
property p1;
    @(posedge rclk) (g_wptr_sync == g_rptr_next) |=> (empty);
endproperty

assert property (p1) else $error("empty failed! -> g_wptr_sync = %b, g_rptr_next = %b, empty = %b",g_wptr_sync, g_rptr_next, empty);

endmodule
