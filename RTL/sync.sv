module sync(input logic rst, clk, 
input logic [5:0] din, 
output logic [5:0] dout);
logic [5:0] q1;
always_ff @(posedge clk or negedge rst) begin
    if(!rst) begin
        ////dout<=0; //BUG: IT SHOULD BE GRAY CODE OF 9 
        //q1<=0; //BUG: IT SHOULD BE GRAY CODE OF 9
	dout <= 6'b001101;
	q1 <= 6'b001101; 
    end
    else begin
        q1<=din;
        dout<=q1;
    end
end
endmodule
 
