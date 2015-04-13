with Private_Types; use Private_Types;

package Use_Private_Types with SPARK_Mode is
   type P_Simple is private;
   type D_Simple_0 is new Simple (D => 0);
   type D_Simple_1 is new Simple (D => 1);
   type Holder is record
      Content : Simple;
   end record;
   type P_Holder is private;
   type D_Holder_0 is record
      Content : D_Simple_0;
   end record;
   type D_Holder_1 is private;

   procedure ReInit (S : in out P_Simple) with
     Post => D_Zero (S);

   procedure ReInit (S : in out Holder) with
     Post => S.Content.D = 0;

   procedure ReInit (S : in out P_Holder) with
     Post => D_Zero (S);

   procedure ReInit (S : in out D_Holder_0) with
     Post => S.Content.D = 0;

   procedure ReInit (S : in out D_Holder_1) with
     Post => False;

   function D_Zero (S : P_Simple) return Boolean;

   function D_Zero (S : P_Holder) return Boolean;
private
   type P_Simple is new Simple;
   function D_Zero (S : P_Simple) return Boolean is (S.D = 0);
   type P_Holder is record
      Content : P_Simple;
   end record;
   function D_Zero (S : P_Holder) return Boolean is (S.Content.D = 0);
   type D_Holder_1 is record
      Content : D_Simple_1;
   end record;
end Use_Private_Types;
