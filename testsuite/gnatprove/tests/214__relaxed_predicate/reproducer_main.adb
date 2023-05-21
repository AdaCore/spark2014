with Interfaces;


procedure Reproducer_Main
with Spark_Mode => On
is

   subtype ID_Type    is Interfaces.Unsigned_8;
   subtype Value_Type is Interfaces.Unsigned_64;

   type Message_Type is record
      ID    : ID_Type;
      Value : Value_Type;
   end record;

   Null_Message : constant Message_Type := (ID => 0, Value => 0);


   subtype Valid_ID_Type is ID_Type range 0 .. 15;
   subtype Valid_Message_Type is Message_Type
   with
       Dynamic_Predicate => Valid_Message_Type.ID in Valid_ID_Type;

   -----------------------------------------------------------------------------

   procedure Initialize
     (Init    : in     Boolean;
      Msg     :    out Message_Type;
      Success :    out Boolean)
   with
     Relaxed_Initialization => Msg,
     Post => (if Success then Msg'Initialized)
   is
   begin
      Msg     := Null_Message;
      Success := Init;
   end Initialize;

   -----------------------------------------------------------------------------

   My_Msg  : Message_Type with Relaxed_Initialization;
   Success : Boolean;

begin
   Initialize (True, My_Msg, Success);
   if Success then
      -- "medium: predicate check might fail, cannot prove upper bound for My_Msg"
      if My_Msg in Valid_Message_Type then
         My_Msg.Value := 1;
      else
         My_Msg := Null_Message;
      end if;
   end if;
end Reproducer_Main;
