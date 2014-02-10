package body Segway
  with SPARK_Mode,
       Refined_State => (State => (Speed, Status))
is
   ----------------------------------------------------
   --         SPARK 2014 - Segway Example            --
   --                                                --
   -- This example illustrates the use of Ada2012    --
   -- expression functions to specify an invariant   --
   -- that must be maintained in a state-machine     --
   -- package                                        --
   ----------------------------------------------------

   --  Actual concrete states are declared here in the body
   --  to prevent direct tampering by clients
   Speed  : Speed_Type;
   Status : Status_Type;

   --------------------
   -- Current_Status --
   --------------------

   function Current_Status return Status_Type is (Status)
     with Refined_Global => Status;

   -------------------
   -- Current_Speed --
   -------------------

   function Current_Speed return Speed_Type is (Speed)
     with Refined_Global => Speed;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     with Refined_Global => (Output => (Status, Speed)),
          Refined_Depends => ((Status, Speed) => null),
          Refined_Post    => Status = Still and Speed = 0
   is
   begin
      Status := Still;
      Speed  := 0;
   end Initialize;

   ------------------
   -- State_Update --
   ------------------

   procedure State_Update (I : Valid_Input)
     with Refined_Global => (In_Out => (Status, Speed)),
          Refined_Depends => (Speed => (Speed, I),
                              Status => (Status, Speed, I))
   is
   begin
      case I is
         when Nothing =>
            null;
         when Accelerate =>
            if Speed < Speed_Type'Last then
               Speed := Speed + 1;
            end if;
         when Brake =>
            if Speed > Speed_Type'First then
               Speed := Speed - 1;
            end if;
      end case;
      if Speed = 0 then
         Status := Still;
      elsif Speed = 1 and then I = Accelerate then
         Status := Forward;
      elsif Speed = -1 and then I = Brake then
         Status := Backward;
      end if;
   end State_Update;

   ----------
   -- Halt --
   ----------

   procedure Halt
     with Refined_Global => (In_Out => (Status, Speed)),
          Refined_Depends => (Speed => (Speed, Status),
                              Status => (Speed, Status))
   is
   begin
      while Status /= Still loop
         pragma Loop_Invariant (Speed_Is_Valid);
         if Speed > 0 then
            State_Update (Brake);
         else
            State_Update (Accelerate);
         end if;
      end loop;
   end Halt;

end Segway;
