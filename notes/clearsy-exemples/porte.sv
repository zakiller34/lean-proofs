module porte (
    input  wire       clk, rst,
    input  wire       cmd_ouvrir, cmd_fermer,
    input  wire [3:0] acc, frein,
    output reg        ouverte,
    output reg  [7:0] vitesse
);
    always @(posedge clk) begin
        if (rst) begin
            ouverte <= 1'b0;
            vitesse <= 8'd0;
        end else begin
            if (cmd_ouvrir && vitesse == 0) ouverte <= 1'b1;
            else if (cmd_fermer)            ouverte <= 1'b0;
`ifdef CORRIGE
            if (!ouverte && !(cmd_ouvrir && vitesse == 0) && acc != 0
                && vitesse <= 8'd255 - acc)
`else
            if (!ouverte && acc != 0 && vitesse <= 8'd255 - acc)
`endif
                vitesse <= vitesse + acc;
            else if (frein <= vitesse)
                vitesse <= vitesse - frein;
        end
    end

`ifdef FORMAL
    reg init = 1'b1;
    always @(posedge clk) init <= 1'b0;
    always @(*) if (init) assume(rst);
    // Même invariant que la machine B : vitesse > 0 => porte fermée
    always @(*) if (!init) assert(!(vitesse != 0 && ouverte));
`endif
endmodule
