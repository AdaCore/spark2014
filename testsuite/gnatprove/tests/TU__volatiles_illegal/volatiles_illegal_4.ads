with System.Storage_Elements;

package Volatiles_Illegal_4
  --  TU: 11. If a procedure has an **in** mode parameter of an
  --  effectively volatile type, then the Effective_Reads aspect of
  --  any corresponding actual parameter shall be False.  [This is
  --  because the parameter is passed by reference and the
  --  corresponding aspect of the formal parameter is False. In the 11
  --  other cases, the volatility refining aspect of the formal
  --  parameter is True and so the aspect of the corresponding actual
  --  parameter may be either True or False.]
  with SPARK_Mode
is
   A : Integer;

   B : Integer
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#B0B0#);

   type Vol_Rec_T is record
      X : Integer := 0;
   end record with Volatile;

   Vol1 : Vol_Rec_T
     with Address => System.Storage_Elements.To_Address (16#ABC0#);

   Vol2 : Vol_Rec_T
     with Async_Writers,
          Address => System.Storage_Elements.To_Address (16#ABCD0#);

   procedure P1 (Par : in Vol_Rec_T ; Par2 : out Integer);
   --  Par must have Async_Writers => True and Effective_Reads => False.

   procedure P2 (Par : out Vol_Rec_T);
   --  Par must have Async_Readers => True.

   procedure P3 (Par : in out Vol_Rec_T);
   --  Par must have all attributes set to True.

   procedure P4 (X : in out Integer);
   --  The formal parameter is a non-Volatile so actual parameters
   --  must also be non-Volatiles.
end Volatiles_Illegal_4;
