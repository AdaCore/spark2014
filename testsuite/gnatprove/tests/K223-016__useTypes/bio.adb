package body Bio
is
   function K (X, Y : IandATypes.TemplateT) return IandATypes.TemplateT
   is
   begin
      return X + Y;
   end K;

end Bio;
