with Sc_Status_Type;

package body Achiever with SPARK_Mode is


   State_Item : Sc_Status_Type.Object_Type;

   function Get_State_Item return Sc_Status_Type.Object_Type is (State_Item);

    --$  function Prf_Do_Something (
    --$     St : St_Type;
    --$     Op : Op_Type;
    --$     Internal_State_Before : Internal_State_Type;
    --$     Internal_State__After : Internal_State_Type;
    --$  )
    --$  return Boolean;

   
       procedure Do_Something (St : in St_Type;
                               Op : Op_Type) is
    --$ global
    --$    in out Internal_State
    --$ ;
    --$ derives
    --$         Internal_State
    --$         from
    --$                 *,
    --$                 St,
    --$                 Op
    --$ ;
    --$ post
    --$ (
    --$      detailed do_something post condition
    --$ )
    --$ and
    --$    Prf_Do_something (
    --$         st,
    --$         Op,
    --$         Internal_State~,
    --$         Internal_State,
    --$    );

       begin
       
       null;
       
       end Do_Something;
       
       procedure Do_Stuff(St :in St_Type)
     --$ global
    --$    in out State_Item,
    --$           Internal_State
    --$ ;
    --$ derives
    --$         Internal_State
    --$         from
    --$                 *,
    --$                 St
    --$         &
    --$         State_Item
    --$         from
    --$                 *
    --$ ;
    --$ post
    --$ (
    --$    (
    --$      not Sc_Status_type.Read(State_Item~)
    --$      and
    --$      Prf_Do_something (
    --$         St,
    --$         Op_1,
    --$         Internal_State~,
    --$         Internal_State)
    --$    )
    --$    or
    --$    (
    --$       Sc_Status_type.Read(State_Item~)
    --$       and
    --$       State_Item = State_Item~
    --$ )
    --$ and
    --$    Prf_Do_Stuff (
    --$         st,
    --$         Internal_State~,
    --$         Internal_State,
    --$    );
      is 
       begin
       
       if not Sc_Status_type.Read(This => State_Item) then
       
       
          Sc_Status_type.Write(This => State_Item, Data => True);
          
          Do_something(St => St,
                       Op => op_1);
        
       
       end if;
       
       end Do_Stuff;
       
       procedure  init is begin
               
           
           State_Item := Sc_Status_Type.Initialise;
               
       end init;

end Achiever;
