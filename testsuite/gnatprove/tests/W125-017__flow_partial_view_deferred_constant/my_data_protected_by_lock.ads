with System;

generic
   type Data_Type is private;
   Data_Address : System.Address;

package My_Data_Protected_By_Lock with SPARK_Mode,
  Abstract_State =>
    (Lock_State,
     --  Thread local vision of the state of the lock, I have it or not
     (Global_Data with External => Async_Writers),
     --  Shared data with mutiple writers and readers
     (Global_Lock_State with External => Async_Writers)),
     --  Shared state of the lock
  Initializes => (Lock_State, Data),
  Initial_Condition => Get_State_For_Calling_Task = Unknown,
  Annotate => (GNATprove, Always_Return)
is

   type Data_Holder (<>) is limited private;
   type Data_Holder_Access is not null access Data_Holder;
   Data : constant Data_Holder_Access;

   type Lock_Status is (Locked, Unknown);
   function Get_State_For_Calling_Task return Lock_Status with
     Ghost,
     Global => Lock_State;

   procedure Lock (Success : out Boolean) with
     Global => (In_Out => (Lock_State, Global_Lock_State, Data),
                Input  => Global_Data),
     Pre  => Get_State_For_Calling_Task = Unknown,
     Post => (if Success then Get_State_For_Calling_Task = Locked
              else Get_State_For_Calling_Task = Unknown);
   --  Acquire the lock. The effect on Data while the object was unlocked are
   --  modeled by a dependency from Global_Data to Data.

   procedure Unlock with
     Global => (In_Out => (Lock_State, Global_Lock_State, Global_Data),
                Input  => Data),
     Pre  => Get_State_For_Calling_Task = Locked,
     Post => Get_State_For_Calling_Task = Unknown;
   --  Release the lock. The effect on Data visible in other threads while the
   --  object was locked are modeled by a dependency from Data to Global_Data.

   function At_End (X : access constant Data_Type) return access constant Data_Type is
     (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End (M : access constant Data_Holder) return access constant Data_Holder is
     (M)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Get_RW_Access (M : not null access Data_Holder) return not null access Data_Type with
     Global => (Proof_In => Lock_State),
     Pre  => Get_State_For_Calling_Task = Locked,
     Post => Get_R_Access (At_End (M)).all = At_End (Get_RW_Access'Result).all;

   function Get_R_Access (M : not null access constant Data_Holder) return not null access constant Data_Type with
     Global => (Proof_In => Lock_State),
     Pre => Get_State_For_Calling_Task = Locked;

private
   pragma SPARK_Mode (Off);

   type Data_Access is not null access all Data_Type;

   type Data_Holder is limited record
      The_Data : Data_Access;
   end record;

   --  Set Data to an alias of the global data you want to encapsulate
   --  however you want.

   My_Data : aliased Data_Type with
     Import,
     Address => Data_Address;

   Data : constant Data_Holder_Access :=
     new Data_Holder'(The_Data => My_Data'Unchecked_Access);
end My_Data_Protected_By_Lock;
