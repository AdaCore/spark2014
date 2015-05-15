package Model is
   type Name_T is new Natural;
   No_Name : constant Name_T := 0;

   -----------
   -- State --
   -----------

   type UML_State is record
      Name_Data : Name_T;
   end record;
   type UML_State_Access is new Integer range 0 .. 100;
   type UML_State_Vector is array (UML_State_Access) of UML_State;

   function Name (Self : UML_State) return Name_T is (Self.Name_Data);

   ----------------
   -- Transition --
   ----------------

   type UML_Transition is record
      From_Data, To_Data : UML_State_Access;
   end record;
   type UML_Transition_Access is new Integer range 0 .. 100;
   type UML_Transition_Vector is
     array (UML_Transition_Access) of UML_Transition;

   --  Setters/getters --

   function From (Self : UML_Transition) return UML_State_Access is
      (Self.From_Data);
   function To   (Self : UML_Transition) return UML_State_Access is
      (Self.To_Data);
   procedure Set_From
     (Self : in out UML_Transition; Val : UML_State_Access)
   with
     Post => From(Self) = Val;
   procedure Set_To
     (Self : in out UML_Transition; Val : UML_State_Access)
   with
     Post => To(Self) = Val;

   -------------------
   -- State Machine --
   -------------------

   type UML_State_Machine is record
      Owned_State_Data      : UML_State_Vector;
      Owned_Transition_Data : UML_Transition_Vector;
   end record;
   type UML_State_Machine_Access is new Integer range 0 .. 100;

   --  Setters/getters --

   function Owned_State (Self : UML_State_Machine) return UML_State_Vector is
      (Self.Owned_State_Data);
   function Owned_Transition
      (Self : UML_State_Machine) return UML_Transition_Vector is
      (Self.Owned_Transition_Data);
   procedure Set_Owned_State
     (Self : in out UML_State_Machine;
      Val  : UML_State_Vector)
   with
     Post => Owned_State(Self) = Val;
   procedure Set_Owned_Transition
     (Self : in out UML_State_Machine;
      Val  : UML_Transition_Vector)
   with
     Post => Owned_Transition(Self) = Val;

   ------------
   -- Action --
   ------------

   type UML_Action is record
      Name_Data : Name_T;
   end record;
   No_UML_Action : constant UML_Action := (Name_Data => No_Name);
   type UML_Action_Access is new Integer range 0 .. 100;
   No_UML_Action_Access : constant UML_Action_Access := 0;
   type UML_Action_Vector is array (UML_Action_Access) of UML_Action;
   No_UML_Action_Vector : constant UML_Action_Vector :=
     (others => No_UML_Action);

   function Name (Self : UML_Action) return Name_T is (Self.Name_Data);

   ------------------
   -- Control_Flow --
   ------------------

   type UML_Control_Flow is record
      From_Data, To_Data : UML_Action_Access;
   end record;
   No_UML_Control_Flow : constant UML_Control_Flow :=
     (From_Data => No_UML_Action_Access, To_Data => No_UML_Action_Access);
   type UML_Control_Flow_Access is new Integer range 0 .. 100;
   type UML_Control_Flow_Vector is
     array (UML_Control_Flow_Access) of UML_Control_Flow;
   No_UML_Control_Flow_Vector : constant UML_Control_Flow_Vector :=
     (others => No_UML_Control_Flow);

   --  Setters/getters --

   function From (Self : UML_Control_Flow) return UML_Action_Access is
      (Self.From_Data);
   function To   (Self : UML_Control_Flow) return UML_Action_Access is
      (Self.To_Data);
   procedure Set_From
     (Self : in out UML_Control_Flow; Val : UML_Action_Access)
   with
     Post => From(Self) = Val and To(Self) = To(Self)'Old;
   procedure Set_To
     (Self : in out UML_Control_Flow; Val : UML_Action_Access)
   with
     Post => To(Self) = Val and From(Self) = From(Self)'Old;

   --------------
   -- Activity --
   --------------

   type UML_Activity is record
      Owned_Action_Data : UML_Action_Vector;
      Owned_Flow_Data   : UML_Control_Flow_Vector;
   end record;
   No_UML_Activity : constant UML_Activity :=
     (Owned_Action_Data => No_UML_Action_Vector,
      Owned_Flow_Data => No_UML_Control_Flow_Vector);
   type UML_Activity_Access is new Integer range 0 .. 100;

   --  Setters/getters --

   function Owned_Action (Self : UML_Activity) return UML_Action_Vector is
      (Self.Owned_Action_Data);
   function Owned_Flow
      (Self : UML_Activity) return UML_Control_Flow_Vector is
      (Self.Owned_Flow_Data);
   procedure Set_Owned_Action
     (Self : in out UML_Activity;
      Val  : UML_Action_Vector)
   with
     Post => Owned_Action(Self) = Val and
     Owned_Flow(Self) = Owned_Flow(Self'Old);
   procedure Set_Owned_Flow
     (Self : in out UML_Activity;
      Val  : UML_Control_Flow_Vector)
   with
     Post => Owned_Flow(Self) = Val and
     Owned_Action(Self) = Owned_Action(Self'Old);

   ---------------------
   -- Transformations --
   ---------------------

   --  Here the property that we want to prove is that, for each transition
   --  in a state machine, we have a control flow in an activity and that
   --  the actions connected in the activity "correspond" to the states
   --  connected by the transition. The "corresponsing relation" is trivially
   --  satisfied if the two elements have the same name.

   function Transform
     (SM : UML_State_Machine) return UML_Activity
   with Post =>
     (for all T in Owned_Transition(SM)'Range =>
--        (for some K in Owned_Flow(Transform'Result)'Range =>
           Name(Owned_State(SM)(From(Owned_Transition(SM)(T)))) =
             Name(Owned_Action(Transform'Result)
               (From(Owned_Flow(Transform'Result)
                 (UML_Control_Flow_Access(T)))))
           and then
           Name(Owned_State(SM)(To(Owned_Transition(SM)(T)))) =
             Name(Owned_Action(Transform'Result)
               (To(Owned_Flow(Transform'Result)
                 (UML_Control_Flow_Access(T))))));

end Model;
