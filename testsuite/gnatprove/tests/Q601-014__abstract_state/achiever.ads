with Sc_Status_Type;
use type Sc_Status_Type.Object_Type;

package Achiever with SPARK_Mode is

  type St_Type is mod 2**4;
  for St_Type'Size use 4;

   type Op_Type is (Op_1, Op_2, Op_3, Op_4);

    --$  function Prf_Do_Stuff (
    --$     St : St_Type;
    --$     Internal_State_Before : Internal_State_Type;
    --$     Internal_State__After : Internal_State_Type;
    --$  )
    --$  return Boolean;

   type Internal_State is private;

   function Get_Internal_State return Internal_State;

   function Get_State_Item return Sc_Status_Type.Object_Type;

   function Prf_Do_Something (St     : St_Type;
                              Op     : Op_Type;
                              Before : Internal_State;
                              After  : Internal_State) return Boolean;


   function Prf_Do_Stuff (St     : St_Type;
                          Before : Internal_State;
                          After  : Internal_State) return Boolean;

   procedure Do_Stuff (St :in St_Type) with
     Contract_Cases =>
       (not Sc_Status_type.Read(Get_State_Item) =>
          Prf_Do_Something (
            St,
            Op_1,
            Get_Internal_State'Old,
            Get_Internal_State)
          and
          Sc_Status_type.Read(Get_State_Item),
        Sc_Status_Type.Read(Get_State_Item) =>
          Get_State_Item = Get_State_Item'Old),
     Post =>
       Prf_Do_Stuff (
            st,
            Get_Internal_State'Old,
            Get_Internal_State);

   procedure  init;

private
   type Internal_State is new Integer;

   function Get_Internal_State return Internal_State is (0);

   function Prf_Do_Something (St     : St_Type;
                              Op     : Op_Type;
                              Before : Internal_State;
                              After  : Internal_State) return Boolean is (True);


   function Prf_Do_Stuff (St     : St_Type;
                          Before : Internal_State;
                          After  : Internal_State) return Boolean is (True);

end Achiever;
