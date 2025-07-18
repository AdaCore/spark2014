procedure Potentially_Invalid_Warning with spark_mode is
   type Int_8 is range -128 .. 127 with Size => 8;
   subtype Pos_8 is Int_8 range 1 .. 127;

   function One_OK return Pos_8 with
     Potentially_Invalid => One_OK'Result,
     Post => One_OK'Result'Valid and then One_OK'Result = 1,
     Import;

   function One_Bad return Pos_8 with
     Potentially_Invalid => One_Bad'Result,
     Post => not One_Bad'Result'Valid and then One_Bad'Result = -1,
     Import;
begin
  null;
end;
