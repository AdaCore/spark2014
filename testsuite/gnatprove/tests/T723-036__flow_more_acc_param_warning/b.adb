procedure B with SPARK_Mode
is

   --  This test is based loosely on ACATS test C41303S
   --  which is about "ACCESS TO ACCESS TO SCALAR"
   --  This generates a number of legitimate SPARK errors,
   --  however we care about the warning from R_ASSIGN.

   TYPE  NEWINT  IS  NEW INTEGER ;

   TYPE  ACCNEWINT  IS  ACCESS NEWINT ;

   ACCNEWINT_CONST : ACCNEWINT :=  NEW NEWINT'( 813 );
   ACCNEWINT_VAR   : ACCNEWINT :=  ACCNEWINT_CONST  ;
   ACCNEWINT_VAR0  : ACCNEWINT :=  ACCNEWINT_CONST  ;

   TYPE ACC_ACCNEWINT IS ACCESS ACCNEWINT ;

   ACC_ACCNEWINT_VAR  : ACC_ACCNEWINT := new ACCNEWINT'(ACCNEWINT_CONST);
   ACC_ACCNEWINT_VAR0 : ACC_ACCNEWINT := new ACCNEWINT'(ACCNEWINT_CONST);

   PROCEDURE R_ASSIGN(R_IN   : in     ACCNEWINT;
                      R_INOUT : in out ACCNEWINT)
   is
      --  Should generate a warning saying that R_IN is unchanged and
      --  its type can be replaced by 'access constant NEWINT'
   begin
      ACCNEWINT_VAR  := R_IN    ;
      ACCNEWINT_VAR0 := R_INOUT ;
   end R_ASSIGN;
begin
   R_ASSIGN(ACC_ACCNEWINT_VAR.ALL,
            ACC_ACCNEWINT_VAR0.ALL);
END B;
