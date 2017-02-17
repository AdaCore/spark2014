package body DevTest
is

   Vol_AW : Integer with Volatile, Async_Writers;

   Vol_AW_ER : Integer with Volatile, Async_Writers, Effective_Reads;

   procedure AW_Test_Dup_Read (X, Y : out Integer;
                               B    : Boolean)
   with Global => (Input => Vol_AW),
        Depends => (X => (B, Vol_AW),
                    Y => Vol_AW)
   is
   begin
      if B then
         X := Vol_AW;
      else
         X := 0;
      end if;
      Y := Vol_AW;
   end AW_Test_Dup_Read;

   procedure AW_ER_Test_Dup_Read (X, Y : out Integer;
                                  B    : Boolean)
   with Global => (In_Out => Vol_AW_ER),
        Depends => (X         => (B, Vol_AW_ER),
                    Y         => (B, Vol_AW_ER),
                    Vol_AW_ER => (Vol_AW_ER, B))
   is
   begin
      if B then
         X := Vol_AW_ER;
      else
         X := 0;
      end if;
      Y := Vol_AW_ER;
   end AW_ER_Test_Dup_Read;

   procedure AW_ER_Test_Loop_Read (X     :    out Integer;
                                   Event : in out Integer)
   with Global => (In_Out => Vol_AW_ER),
        Depends => (X         => Vol_AW_ER,
                    Vol_AW_ER => Vol_AW_ER,
                    Event     => (Event, Vol_AW_ER))
   is
   begin
      loop
         X := Vol_AW_ER;
         Event := Event;
         exit when X >= 0;
      end loop;
   end AW_ER_Test_Loop_Read;

begin
   Vol_AW    := 0;
   Vol_AW_ER := 0;
end DevTest;
