procedure Range_Check_Aggr with Spark_Mode is

   type NUMBER is range 1 .. 100 ;

   generic

      type INTEGER_TYPE is range <> ;
      F_STATIC_VALUE : in INTEGER_TYPE ;
      S_STATIC_VALUE : in INTEGER_TYPE ;
      T_STATIC_VALUE : in INTEGER_TYPE ;
      L_STATIC_VALUE : in INTEGER_TYPE ;

   procedure PC (LOWER  : in INTEGER_TYPE ;
                 UPPER  : in INTEGER_TYPE) ;

   procedure PC (LOWER  : in INTEGER_TYPE ;
                 UPPER  : in INTEGER_TYPE) is

      subtype SUBINTEGER_TYPE is INTEGER_TYPE
      range LOWER .. UPPER ;
      type AR1 is array (INTEGER range 1..3) of
        SUBINTEGER_TYPE ;
      type REC is
         record
            FIRST  : SUBINTEGER_TYPE ;
            SECOND : AR1 ;
         end record;

      procedure PC1 (R : REC := (F_STATIC_VALUE,
                                 (S_STATIC_VALUE,
                                  T_STATIC_VALUE,
                                  L_STATIC_VALUE))) is
      begin  -- PC1
         null;
      end PC1;

   begin  -- PC
      PC1;
   end PC;

   procedure NEW_PC is new PC (INTEGER_TYPE => NUMBER,
                               F_STATIC_VALUE => 15,
                               S_STATIC_VALUE => 19,
                               T_STATIC_VALUE => 85,
                               L_STATIC_VALUE => 99) ;

begin   -- REC_NON_STAT_COMPS
   NEW_PC (LOWER => 20,
           UPPER => 80);

end Range_Check_Aggr;
