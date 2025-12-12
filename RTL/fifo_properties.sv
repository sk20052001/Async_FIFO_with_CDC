module fifo_properties#(parameter data_width = 8) (input logic [data_width-1:0] data_in,
  input logic w_en, r_en, w_clk, r_clk,wrst_n,rrst_n,
  input logic full,empty,
  input logic [data_width-1:0] data_out,
 // Internal signals for verification
  input logic [5:0] b_wptr, b_rptr,
  input logic [5:0] g_wptr, g_rptr,
  input logic [5:0] g_wptr_sync, g_rptr_sync
);

    //=================================================================
    // ASSUMPTIONS for Formal Verification
    //=================================================================
    
    // Assume control signals don't have X values after reset
    property assume_wen_no_x;
        @(posedge w_clk)
        wrst_n |-> !$isunknown(w_en);
    endproperty
    assume property (assume_wen_no_x);
    
    property assume_ren_no_x;
        @(posedge r_clk)
        rrst_n |-> !$isunknown(r_en);
    endproperty
    assume property (assume_ren_no_x);
    
    // Assume data_in doesn't have X values when writing
    property assume_data_in_no_x;
        @(posedge w_clk)
        (wrst_n && w_en) |-> !$isunknown(data_in);
    endproperty
    assume property (assume_data_in_no_x); 
   
    //=================================================================
    // X-VALUE CHECKING PROPERTIES
    // These catch uninitialized signals early
    //=================================================================
    
    property p_no_x_wptr;
        @(posedge w_clk)
        wrst_n |-> !$isunknown(b_wptr);
    endproperty
    
    assert_no_x_wptr: assert property(p_no_x_wptr)
        else $error("X-VALUE: Write pointer has X value");
    
    property p_no_x_rptr;
        @(posedge r_clk)
        rrst_n |-> !$isunknown(b_rptr);
    endproperty
    
    assert_no_x_rptr: assert property(p_no_x_rptr)
        else $error("X-VALUE: Read pointer has X value");
    
    property p_no_x_full;
        @(posedge w_clk)
        wrst_n |-> !$isunknown(full);
    endproperty
    
    assert_no_x_full: assert property(p_no_x_full)
        else $error("X-VALUE: Full flag has X value");
    
    property p_no_x_empty;
        @(posedge r_clk)
        rrst_n |-> !$isunknown(empty);
    endproperty
    
    assert_no_x_empty: assert property(p_no_x_empty)
        else $error("X-VALUE: Empty flag has X value");
	
   //=================================================================
   // PROPERTY 1: No Write Overflow
   // Writing should only happen when FIFO is not full
   //=================================================================
    property p_no_overflow;
        @(posedge w_clk) disable iff (!wrst_n)
        (!$isunknown(w_en) && full && w_en) |-> ##1 $stable(b_wptr);
    endproperty
    
    assert_no_overflow: assert property(p_no_overflow)
        else $error("OVERFLOW: Write attempted when FIFO is full");

    // Alternative property: Check that write only happens when not full
    property p_write_when_not_full;
        @(posedge w_clk) disable iff (!wrst_n)
        (w_en && !$stable(b_wptr)) |-> !$past(full);
    endproperty
    
    assert_write_when_not_full: assert property(p_write_when_not_full)
        else $error("OVERFLOW: Write pointer changed when FIFO was full"); 
	
    cover_overflow_attempt: cover property(
        @(posedge w_clk) (full && w_en)
    );

    //=================================================================
    // PROPERTY 2: No Read Underflow
    // Reading should only happen when FIFO is not empty
    //=================================================================
    property p_no_underflow;
        @(posedge r_clk) disable iff (!rrst_n)
        (!$isunknown(r_en) && r_en && empty && $past(empty) && $past(empty,2)) |->  ##1 $stable(b_rptr);
    endproperty
    
    assert_no_underflow: assert property(p_no_underflow)
        else $error("UNDERFLOW: Read attempted when FIFO is empty");
    
    cover_underflow_attempt: cover property(
        @(posedge r_clk) (empty && r_en)
    );

    //=================================================================
    // PROPERTY 3: Gray Code Single Bit Change
    // Gray code should change only 1 bit at a time
    //=================================================================
    function automatic int count_bit_changes(logic [5:0] a, b);
        logic [5:0] xor_result;
        int count;
        xor_result = a ^ b;
        count = 0;
        for (int i = 0; i < 6; i++) begin
            if (xor_result[i]) count++;
        end
        return count;
    endfunction

    property p_gray_wptr_single_bit;
        @(posedge w_clk) disable iff (!wrst_n)
        !$stable(g_wptr) |-> (count_bit_changes($past(g_wptr), g_wptr) == 1);
    endproperty
    
    assert_gray_wptr: assert property(p_gray_wptr_single_bit)
        else $error("GRAY: Write gray code changed more than 1 bit");

    property p_gray_rptr_single_bit;
        @(posedge r_clk) disable iff (!rrst_n)
        !$stable(g_rptr) |-> (count_bit_changes($past(g_rptr), g_rptr) == 1);
    endproperty
    
    assert_gray_rptr: assert property(p_gray_rptr_single_bit)
        else $error("GRAY: Read gray code changed more than 1 bit");

    //=================================================================
    // PROPERTY 4: Pointer Range Check
    // Pointers should always be in valid range [9:54]
    //=================================================================
    property p_wptr_range;
        @(posedge w_clk) disable iff (!wrst_n)
        (b_wptr >= 6'd9) && (b_wptr <= 6'd54);
    endproperty
    
    assert_wptr_range: assert property(p_wptr_range)
        else $error("WPTR: Write pointer out of range: %d", b_wptr);

    property p_rptr_range;
        @(posedge r_clk) disable iff (!rrst_n)
        (b_rptr >= 6'd9) && (b_rptr <= 6'd54);
    endproperty
    
    assert_rptr_range: assert property(p_rptr_range)
        else $error("RPTR: Read pointer out of range: %d", b_rptr);

    //=================================================================
    // PROPERTY 5: Write Pointer Increment
    // Write pointer should increment when writing and not full
    //=================================================================
    property p_wptr_increment;
        @(posedge w_clk) disable iff (!wrst_n)
        (w_en && !full && wrst_n) |-> 
            ##1 ((b_wptr == 6'd9 && $past(b_wptr) == 6'd54) || 
                 (b_wptr == $past(b_wptr) + 1));
    endproperty
    
    assert_wptr_increment: assert property(p_wptr_increment)
        else $error("WPTR: Write pointer increment failed at time %0t, b_wptr=%0d, past=%0d", 
                    $time, b_wptr, $past(b_wptr));

    //=================================================================
    // PROPERTY 6: Read Pointer Increment
    // Read pointer should increment when reading and not empty
    //=================================================================
    property p_rptr_increment;
        @(posedge r_clk) disable iff (!rrst_n)
	 !$stable(b_rptr) |-> 
            ((($past(b_rptr) == 6'd54) && (b_rptr == 6'd9)) ||
            (b_rptr == $past(b_rptr) + 6'd1));
    endproperty
    
    assert_rptr_increment: assert property(p_rptr_increment)
        else $error("RPTR: Read pointer increment failed");


    //=================================================================
    // COVERAGE PROPERTIES
    //=================================================================
    cover_full: cover property(
        @(posedge w_clk) full
    );
    
    cover_empty: cover property(
        @(posedge r_clk) empty
    );
    
    cover_simultaneous_rw: cover property(
        @(posedge w_clk) (w_en && !full) ##0 @(posedge r_clk) (r_en && !empty)
    );
    
    cover_wrap_around_write: cover property(
        @(posedge w_clk) (b_wptr == 6'd54) ##1 (b_wptr == 6'd9)
    );
    
    cover_wrap_around_read: cover property(
        @(posedge r_clk) (b_rptr == 6'd54) ##1 (b_rptr == 6'd9)
    );

endmodule 


bind top fifo_properties #(.data_width(data_width)) fifo_props(.*);
