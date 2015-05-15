package body Model is

   procedure Set_From
     (Self : in out UML_Transition; Val : UML_State_Access) is
   begin
      Self.From_Data := Val;
   end Set_From;

   procedure Set_To
     (Self : in out UML_Transition; Val : UML_State_Access) is
   begin
      Self.To_Data := Val;
   end Set_To;

   procedure Set_Owned_State
     (Self : in out UML_State_Machine;
      Val  : UML_State_Vector) is
   begin
      Self.Owned_State_Data := Val;
   end Set_Owned_State;

   procedure Set_Owned_Transition
     (Self : in out UML_State_Machine;
      Val  : UML_Transition_Vector) is
   begin
      Self.Owned_Transition_Data := Val;
   end Set_Owned_Transition;

   procedure Set_From
     (Self : in out UML_Control_Flow; Val : UML_Action_Access) is
   begin
      Self.From_Data := Val;
   end Set_From;

   procedure Set_To
     (Self : in out UML_Control_Flow; Val : UML_Action_Access) is
   begin
      Self.To_Data := Val;
   end Set_To;

   procedure Set_Owned_Action
     (Self : in out UML_Activity;
      Val  : UML_Action_Vector) is
   begin
      Self.Owned_Action_Data := Val;
   end Set_Owned_Action;

   procedure Set_Owned_Flow
     (Self : in out UML_Activity;
      Val  : UML_Control_Flow_Vector) is
   begin
      Self.Owned_Flow_Data := Val;
   end Set_Owned_Flow;

   function Transform (SM : UML_State_Machine) return UML_Activity is
      AV  : UML_Action_Vector := No_UML_Action_Vector;
      CFV : UML_Control_Flow_Vector := No_UML_Control_Flow_Vector;
      Act : UML_Activity := No_UML_Activity;
   begin
      for S in Owned_State(SM)'Range loop
	 pragma Loop_Invariant
	   (for all T in Owned_State(SM)'First .. S-1 =>
	      Name(Owned_State(SM)(T)) =
	      Name(AV(UML_Action_Access(T))));

	 AV(UML_Action_Access(S)) :=
	   UML_Action'(Name_Data => Name(Owned_State(SM)(S)));
      end loop;

      for S in Owned_Transition(SM)'Range loop
         pragma Loop_Invariant
           (for all T in Owned_Transition(SM)'First .. S-1 =>
              Name(Owned_State(SM)(From(Owned_Transition(SM)(T)))) =
              Name(AV(From(CFV(UML_Control_Flow_Access(T)))))
            and
              Name(Owned_State(SM)(To(Owned_Transition(SM)(T)))) =
              Name(AV(To(CFV(UML_Control_Flow_Access(T))))));

         Set_From (CFV(UML_Control_Flow_Access(S)),
                   UML_Action_Access(From(Owned_Transition(SM)(S))));
         Set_To (CFV(UML_Control_Flow_Access(S)),
                 UML_Action_Access(To(Owned_Transition(SM)(S))));
      end loop;

      Set_Owned_Action (Act, AV);
      Set_Owned_Flow (Act, CFV);
      return Act;
   end Transform;
end Model;
