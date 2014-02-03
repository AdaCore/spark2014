package Initialize_Remote_Stuff
  with SPARK_Mode
  --  TU: 1. In |SPARK| the elaboration of a package shall only update,
  --  directly or indirectly, variables declared immediately within the
  --  package.
is
   procedure Initialize_Remote_Var;

   procedure Initialize_Remote_State;
end Initialize_Remote_Stuff;
