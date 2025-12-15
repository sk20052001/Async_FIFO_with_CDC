# Assertion Based Verifcation of Async_FIFO_with_CDC
This project involves the design and Assertion based verification of a 45-deep Asynchronous FIFO with with 2-stage synchronizers for safe CLock Domain Crossing

## Team Members
Sanjeev Krishnan Kamalamurugan
Aakash Siddharth
Siddesh Patil
Neil Austin Tauro

## Project File Structure

```
+---run
|       |    TCL script for VC Formal FPV and AEP app
+---RTL
|       |    RTL design and SVA files of Asynchronous FIFO with 
```

## To Run
In terminal of the run directory, run the respective tcl file.

## Features & Architecture
45-deep Queue
2 different clock domains
gray code pointers with 2 stage synchronizers

## Verification Strategy
Implemented System Verilog Assumption, Assertion and Cover properties.

## Tools & Setup
VC Formal – FPV and AEP app
System Verilog Assertions
