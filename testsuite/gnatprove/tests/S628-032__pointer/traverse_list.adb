procedure Traverse_List with SPARK_Mode is
    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

    function Get_Nth (X : access List; I : Natural) return access List
with Import;


    procedure Do_Smthing (X : List_Acc)  is
       B : access List := Get_Nth (Get_Nth (X.Next, 2).Next, 1).Next;
    begin
       B := Get_Nth (Get_Nth (B.Next, 2).Next, 1).Next;
       B.Val := 3;
    end Do_Smthing;

begin
    null;
end Traverse_List;
