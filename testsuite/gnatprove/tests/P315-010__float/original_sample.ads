package Original_Sample is

   --------------------------------------------------------------------------------------------
   -- Release used:
   --
   -- GPS 6.2.0 (20151104) hosted on x86_64-pc-linux-gnu
   -- GNAT Pro 17.0w (20151202-49)
   -- CodePeer 3.1.0 (20151104) for Linux 64 bits
   -- OS : Red Hat Enterprise Linux Workstation release 6.3 (2.6.32-279.el6.x86_64)
   --------------------------------------------------------------------------------------------




   function Are_Float_Equal (Float_Tested, Float_Ref : in Float) return Boolean is (Float_Ref /= 0.0 and then abs(Float_Tested - Float_Ref)/Float_Ref < 1.0e-5);

   subtype Nb_Type         is Natural     range 0   .. 100;
   subtype D_Time_Type     is Float       range 0.0 .. 1_000.0;
   subtype Delta_Time_Type is D_Time_Type range 0.0 .. 1.0;

   --------------------------------------------------------------------------------------------
   -- Study_Case:
   --
   -- Two results misunderstood when running GNATProve on this sub-program:
   --
   --    1/ Pre => Time < Float'Last - (Nb_Of_Fp + Nb_Of_Pp) * Delta_Time : still get "overflow
   --    2/ Post    => (if Nb_Of_Fill_Pulse >= 0.0 then Time > Time'Old);
   --------------------------------------------------------------------------------------------
   procedure Study_Case (Nb_Of_Fp     : in     Nb_Type;
                         Nb_Of_Pp     : in     Nb_Type;
                         Delta_Time   : in     Delta_Time_Type;
                         Time         : in out Float) with
     SPARK_Mode,
     Global  => null,
     Depends => (Time => (Nb_Of_Fp, Nb_Of_Pp, Delta_Time, Time)),
     Pre     => Nb_Of_Pp > 0 and Delta_Time > 0.0 and
                Time >= 0.5 * Float (Nb_Of_Fp + Nb_Of_Pp) * Delta_Time and
                Time < Float'Last - Float (Nb_Of_Fp + Nb_Of_Pp) * Delta_Time,
     Post    => (if Nb_Of_Fp > 0 then Time >= Time'Old);

     -- Contract_Cases => (Nb_Of_Fp = 0 => Are_Float_Equal(Time'Old, Time),
     --                    Nb_Of_Fp > 0 => Time > Time'Old);


   subtype Nb_Float_Type         is Float range 0.0 .. 16.0;

   --------------------------------------------------------------------------------------------
   -- Simple_Case:
   --
   -- Simpler case highlighting the "postcondition might fail" result when proving:
   --
   --    => postcondition might fail, cannot prove Time >= Time'Old
   --------------------------------------------------------------------------------------------
   procedure Simple_Case (Nb         : in     Nb_Float_Type;
                          Time       : in out Float) with
     SPARK_Mode,
     Global  => null,
     Pre     => Time > 0.0 and Time < 10.0,
     Post    => Time >= Time'Old;

end Original_Sample;
