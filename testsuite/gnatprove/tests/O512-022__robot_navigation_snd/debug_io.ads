package Debug_IO is

   procedure Put (X : String) with
     Depends => (null => X);  --  Instructs flow analysis that calls to this
                              --  subprogram are expected to have no effect in
                              --  terms of analysis.

   procedure Put_Line (X : String) with
     Depends => (null => X);  --  Instructs flow analysis that calls to this
                              --  subprogram are expected to have no effect in
                              --  terms of analysis.

   procedure New_Line;

end Debug_IO;
