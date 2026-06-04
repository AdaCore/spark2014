with Ada.Real_Time;

procedure Relaxed_Time with SPARK_Mode => On is

    type Time_Rec is record
        Time : Ada.Real_Time.Time;
    end Record;

    procedure Time_Op
        (Out_Time : out Time_Rec)
     with Relaxed_Initialization => Out_Time,
     Post => Out_Time'Initialized
   is
   begin
      Out_Time.Time := Ada.Real_Time.Clock;
   end Time_Op;

   Time_Out : Time_Rec;

begin

   Time_Op (Time_Out);

end Relaxed_Time;
