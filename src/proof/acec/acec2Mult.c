/**CFile****************************************************************

  FileName    [acec2Mult.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acec2Mult.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"
#include "misc/vec/vecMem.h"
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

static unsigned s_FuncTruths[1920] = {
0xF335ACC0, 0xF553CAA0, 0xCF1DB8C0, 0xDD47E288, 0xBB27E488, 0xAF1BD8A0, 0xC1FDBC80, 0xD4D7E828,
0xB2B7E848, 0xA1FBDA80, 0x89EFE680, 0x8E9FE860, 0xF3AC35C0, 0xF5CA53A0, 0xCFB81DC0, 0xDDE24788,
0xBBE42788, 0xAFD81BA0, 0xC1BCFD80, 0xD4E8D728, 0xB2E8B748, 0xA1DAFB80, 0x89E6EF80, 0x8EE89F60,
0xFA3C3C50, 0xFC5A5A30, 0xCB1CF8D0, 0xDE48D278, 0xBE28B478, 0xAD1AF8B0, 0xCBF81CD0, 0xDED24878,
0xBEB42878, 0xADF81AB0, 0x8EE896F0, 0x8E96E8F0, 0xE334ECC4, 0xF660C66C, 0xEE3C3C44, 0xFC66660C,
0xB926EC8C, 0xBE289C6C, 0xE3EC34C4, 0xF6C6606C, 0xB296E8CC, 0xB2E896CC, 0xB9EC268C, 0xBE9C286C,
0xF660A66A, 0xE552EAA2, 0xDE489A6A, 0xD946EA8A, 0xFA66660A, 0xEE5A5A22, 0xD4E896AA, 0xD496E8AA,
0xF6A6606A, 0xE5EA52A2, 0xD9EA468A, 0xDE9A486A, 0x0CCA533F, 0x0AAC355F, 0x30E2473F, 0x22B81D77,
0x44D81B77, 0x50E4275F, 0x3E02437F, 0x2B2817D7, 0x4D4817B7, 0x5E04257F, 0x7610197F, 0x7160179F,
0x0C53CA3F, 0x0A35AC5F, 0x3047E23F, 0x221DB877, 0x441BD877, 0x5027E45F, 0x3E43027F, 0x2B1728D7,
0x4D1748B7, 0x5E25047F, 0x7619107F, 0x7117609F, 0x05C3C3AF, 0x03A5A5CF, 0x34E3072F, 0x21B72D87,
0x41D74B87, 0x52E5074F, 0x3407E32F, 0x212DB787, 0x414BD787, 0x5207E54F, 0x7117690F, 0x7169170F,
0x1CCB133B, 0x099F3993, 0x11C3C3BB, 0x039999F3, 0x46D91373, 0x41D76393, 0x1C13CB3B, 0x09399F93,
0x4D691733, 0x4D176933, 0x4613D973, 0x4163D793, 0x099F5995, 0x1AAD155D, 0x21B76595, 0x26B91575,
0x059999F5, 0x11A5A5DD, 0x2B176955, 0x2B691755, 0x09599F95, 0x1A15AD5D, 0x2615B975, 0x2165B795,
0xF33A5CC0, 0xF55C3AA0, 0xCF2E74C0, 0xDD742E88, 0xBB724E88, 0xAF4E72A0, 0xC2FE7C40, 0xD7D428E8,
0xB7B248E8, 0xA4FE7A20, 0x98FE6E08, 0x9F8E60E8, 0xF35C3AC0, 0xF53A5CA0, 0xCF742EC0, 0xDD2E7488,
0xBB4E7288, 0xAF724EA0, 0xC27CFE40, 0xD728D4E8, 0xB748B2E8, 0xA47AFE20, 0x986EFE08, 0x9F608EE8,
0xF53C3CA0, 0xF35A5AC0, 0xC72CF4E0, 0xD278DE48, 0xB478BE28, 0xA74AF2E0, 0xC7F42CE0, 0xD2DE7848,
0xB4BE7828, 0xA7F24AE0, 0x96F08EE8, 0x968EF0E8, 0xD338DCC8, 0xC66CF660, 0xDD3C3C88, 0xCF6666C0,
0x9B62CEC8, 0x9C6CBE28, 0xD3DC38C8, 0xC6F66C60, 0x96B2CCE8, 0x96CCB2E8, 0x9BCE62C8, 0x9CBE6C28,
0xA66AF660, 0xB558BAA8, 0x9A6ADE48, 0x9D64AEA8, 0xAF6666A0, 0xBB5A5A88, 0x96AAD4E8, 0x96D4AAE8,
0xA6F66A60, 0xB5BA58A8, 0x9DAE64A8, 0x9ADE6A48, 0x0CC5A33F, 0x0AA3C55F, 0x30D18B3F, 0x228BD177,
0x448DB177, 0x50B18D5F, 0x3D0183BF, 0x282BD717, 0x484DB717, 0x5B0185DF, 0x670191F7, 0x60719F17,
0x0CA3C53F, 0x0AC5A35F, 0x308BD13F, 0x22D18B77, 0x44B18D77, 0x508DB15F, 0x3D8301BF, 0x28D72B17,
0x48B74D17, 0x5B8501DF, 0x679101F7, 0x609F7117, 0x0AC3C35F, 0x0CA5A53F, 0x38D30B1F, 0x2D8721B7,
0x4B8741D7, 0x58B50D1F, 0x380BD31F, 0x2D2187B7, 0x4B4187D7, 0x580DB51F, 0x690F7117, 0x69710F17,
0x2CC72337, 0x3993099F, 0x22C3C377, 0x3099993F, 0x649D3137, 0x639341D7, 0x2C23C737, 0x3909939F,
0x694D3317, 0x69334D17, 0x64319D37, 0x634193D7, 0x5995099F, 0x4AA74557, 0x659521B7, 0x629B5157,
0x5099995F, 0x44A5A577, 0x69552B17, 0x692B5517, 0x5909959F, 0x4A45A757, 0x62519B57, 0x652195B7,
0xFCC5A330, 0xFAA3C550, 0xFCD18B0C, 0xEE8BD144, 0xEE8DB122, 0xFAB18D0A, 0xFDC180BC, 0xE8EBD414,
0xE8EDB212, 0xFBA180DA, 0xEF8980E6, 0xE8F98E06, 0xFCA3C530, 0xFAC5A350, 0xFC8BD10C, 0xEED18B44,
0xEEB18D22, 0xFA8DB10A, 0xFD80C1BC, 0xE8D4EB14, 0xE8B2ED12, 0xFB80A1DA, 0xEF8089E6, 0xE88EF906,
0xFAC3C350, 0xFCA5A530, 0xF8D0CB1C, 0xED84E1B4, 0xEB82E1D2, 0xF8B0AD1A, 0xF8CBD01C, 0xEDE184B4,
0xEBE182D2, 0xF8ADB01A, 0xE88EF096, 0xE8F08E96, 0xECC4E334, 0xF990C99C, 0xEEC3C344, 0xFC99990C,
0xEC8CB926, 0xEB82C9C6, 0xECE3C434, 0xF9C9909C, 0xE8CCB296, 0xE8B2CC96, 0xECB98C26, 0xEBC982C6,
0xF990A99A, 0xEAA2E552, 0xED84A9A6, 0xEA8AD946, 0xFA99990A, 0xEEA5A522, 0xE8D4AA96, 0xE8AAD496,
0xF9A9909A, 0xEAE5A252, 0xEAD98A46, 0xEDA984A6, 0x033A5CCF, 0x055C3AAF, 0x032E74F3, 0x11742EBB,
0x11724EDD, 0x054E72F5, 0x023E7F43, 0x17142BEB, 0x17124DED, 0x045E7F25, 0x10767F19, 0x170671F9,
0x035C3ACF, 0x053A5CAF, 0x03742EF3, 0x112E74BB, 0x114E72DD, 0x05724EF5, 0x027F3E43, 0x172B14EB,
0x174D12ED, 0x047F5E25, 0x107F7619, 0x177106F9, 0x053C3CAF, 0x035A5ACF, 0x072F34E3, 0x127B1E4B,
0x147D1E2D, 0x074F52E5, 0x07342FE3, 0x121E7B4B, 0x141E7D2D, 0x07524FE5, 0x17710F69, 0x170F7169,
0x133B1CCB, 0x066F3663, 0x113C3CBB, 0x036666F3, 0x137346D9, 0x147D3639, 0x131C3BCB, 0x06366F63,
0x17334D69, 0x174D3369, 0x134673D9, 0x14367D39, 0x066F5665, 0x155D1AAD, 0x127B5659, 0x157526B9,
0x056666F5, 0x115A5ADD, 0x172B5569, 0x17552B69, 0x06566F65, 0x151A5DAD, 0x152675B9, 0x12567B59,
0xFCCA5330, 0xFAAC3550, 0xFCE2470C, 0xEEB81D44, 0xEED81B22, 0xFAE4270A, 0xFEC2407C, 0xEBE814D4,
0xEDE812B2, 0xFEA4207A, 0xFE98086E, 0xF9E8068E, 0xFC53CA30, 0xFA35AC50, 0xFC47E20C, 0xEE1DB844,
0xEE1BD822, 0xFA27E40A, 0xFE40C27C, 0xEB14E8D4, 0xED12E8B2, 0xFE20A47A, 0xFE08986E, 0xF906E88E,
0xF5C3C3A0, 0xF3A5A5C0, 0xF4E0C72C, 0xE1B4ED84, 0xE1D2EB82, 0xF2E0A74A, 0xF4C7E02C, 0xE1EDB484,
0xE1EBD282, 0xF2A7E04A, 0xF096E88E, 0xF0E8968E, 0xDCC8D338, 0xC99CF990, 0xDDC3C388, 0xCF9999C0,
0xCEC89B62, 0xC9C6EB82, 0xDCD3C838, 0xC9F99C90, 0xCCE896B2, 0xCC96E8B2, 0xCE9BC862, 0xC9EBC682,
0xA99AF990, 0xBAA8B558, 0xA9A6ED84, 0xAEA89D64, 0xAF9999A0, 0xBBA5A588, 0xAA96E8D4, 0xAAE896D4,
0xA9F99A90, 0xBAB5A858, 0xAE9DA864, 0xA9EDA684, 0x0335ACCF, 0x0553CAAF, 0x031DB8F3, 0x1147E2BB,
0x1127E4DD, 0x051BD8F5, 0x013DBF83, 0x1417EB2B, 0x1217ED4D, 0x015BDF85, 0x0167F791, 0x0617F971,
0x03AC35CF, 0x05CA53AF, 0x03B81DF3, 0x11E247BB, 0x11E427DD, 0x05D81BF5, 0x01BF3D83, 0x14EB172B,
0x12ED174D, 0x01DF5B85, 0x01F76791, 0x06F91771, 0x0A3C3C5F, 0x0C5A5A3F, 0x0B1F38D3, 0x1E4B127B,
0x1E2D147D, 0x0D1F58B5, 0x0B381FD3, 0x1E124B7B, 0x1E142D7D, 0x0D581FB5, 0x0F691771, 0x0F176971,
0x23372CC7, 0x3663066F, 0x223C3C77, 0x3066663F, 0x3137649D, 0x3639147D, 0x232C37C7, 0x3606636F,
0x3317694D, 0x3369174D, 0x3164379D, 0x3614397D, 0x5665066F, 0x45574AA7, 0x5659127B, 0x5157629B,
0x5066665F, 0x445A5A77, 0x5569172B, 0x5517692B, 0x5606656F, 0x454A57A7, 0x5162579B, 0x5612597B,
0x3F53CA0C, 0x5F35AC0A, 0x3F47E230, 0x771DB822, 0x771BD844, 0x5F27E450, 0x35F3C0AC, 0x53F5A0CA,
0x34F7E320, 0x717DB282, 0x717BD484, 0x52F7E540, 0x1CDFCB08, 0x4D7D8E82, 0x1DCFC0B8, 0x47DD88E2,
0x46DFD940, 0x4D6FD490, 0x2B7B8E84, 0x1ABFAD08, 0x2B6FB290, 0x26BFB920, 0x27BB88E4, 0x1BAFA0D8,
0x3FCA530C, 0x5FAC350A, 0x3FE24730, 0x77B81D22, 0x77D81B44, 0x5FE42750, 0x35C0F3AC, 0x53A0F5CA,
0x34E3F720, 0x71B27D82, 0x71D47B84, 0x52E5F740, 0x1CCBDF08, 0x4D8E7D82, 0x1DC0CFB8, 0x4788DDE2,
0x46D9DF40, 0x4DD46F90, 0x2B8E7B84, 0x1AADBF08, 0x2BB26F90, 0x26B9BF20, 0x2788BBE4, 0x1BA0AFD8,
0x3C50FA3C, 0x5A30FC5A, 0x3E43F270, 0x7B1278D2, 0x7D1478B4, 0x5E25F470, 0x3CFA503C, 0x5AFC305A,
0x3EF24370, 0x7B7812D2, 0x7D7814B4, 0x5EF42570, 0x1CD0CBF8, 0x4878DED2, 0x1CCBD0F8, 0x48DE78D2,
0x4DD469F0, 0x4D69D4F0, 0x2878BEB4, 0x1AB0ADF8, 0x2B69B2F0, 0x2BB269F0, 0x28BE78B4, 0x1AADB0F8,
0x3E43CE4C, 0x6F066CC6, 0x3C44EE3C, 0x660CFC66, 0x7619DC4C, 0x7D146C9C, 0x34E3C4EC, 0x60F66CC6,
0x34C4E3EC, 0x606CF6C6, 0x7169D4CC, 0x71D469CC, 0x3ECE434C, 0x6F6C06C6, 0x3CEE443C, 0x66FC0C66,
0x76DC194C, 0x7D6C149C, 0x2B698ECC, 0x2B8E69CC, 0x286CBE9C, 0x268CB9EC, 0x26B98CEC, 0x28BE6C9C,
0x6F066AA6, 0x5E25AE2A, 0x7B126A9A, 0x7619BA2A, 0x660AFA66, 0x5A22EE5A, 0x60F66AA6, 0x52E5A2EA,
0x71B269AA, 0x7169B2AA, 0x606AF6A6, 0x52A2E5EA, 0x4D8E69AA, 0x4D698EAA, 0x48DE6A9A, 0x46D98AEA,
0x468AD9EA, 0x486ADE9A, 0x6F6A06A6, 0x5EAE252A, 0x7B6A129A, 0x76BA192A, 0x66FA0A66, 0x5AEE225A,
0xC0AC35F3, 0xA0CA53F5, 0xC0B81DCF, 0x88E247DD, 0x88E427BB, 0xA0D81BAF, 0xCA0C3F53, 0xAC0A5F35,
0xCB081CDF, 0x8E824D7D, 0x8E842B7B, 0xAD081ABF, 0xE32034F7, 0xB282717D, 0xE2303F47, 0xB822771D,
0xB92026BF, 0xB2902B6F, 0xD484717B, 0xE54052F7, 0xD4904D6F, 0xD94046DF, 0xD844771B, 0xE4505F27,
0xC035ACF3, 0xA053CAF5, 0xC01DB8CF, 0x8847E2DD, 0x8827E4BB, 0xA01BD8AF, 0xCA3F0C53, 0xAC5F0A35,
0xCB1C08DF, 0x8E4D827D, 0x8E2B847B, 0xAD1A08BF, 0xE33420F7, 0xB271827D, 0xE23F3047, 0xB877221D,
0xB92620BF, 0xB22B906F, 0xD471847B, 0xE55240F7, 0xD44D906F, 0xD94640DF, 0xD877441B, 0xE45F5027,
0xC3AF05C3, 0xA5CF03A5, 0xC1BC0D8F, 0x84ED872D, 0x82EB874B, 0xA1DA0B8F, 0xC305AFC3, 0xA503CFA5,
0xC10DBC8F, 0x8487ED2D, 0x8287EB4B, 0xA10BDA8F, 0xE32F3407, 0xB787212D, 0xE3342F07, 0xB721872D,
0xB22B960F, 0xB2962B0F, 0xD787414B, 0xE54F5207, 0xD4964D0F, 0xD44D960F, 0xD741874B, 0xE5524F07,
0xC1BC31B3, 0x90F99339, 0xC3BB11C3, 0x99F30399, 0x89E623B3, 0x82EB9363, 0xCB1C3B13, 0x9F099339,
0xCB3B1C13, 0x9F930939, 0x8E962B33, 0x8E2B9633, 0xC131BCB3, 0x9093F939, 0xC311BBC3, 0x9903F399,
0x8923E6B3, 0x8293EB63, 0xD4967133, 0xD4719633, 0xD7934163, 0xD9734613, 0xD9467313, 0xD7419363,
0x90F99559, 0xA1DA51D5, 0x84ED9565, 0x89E645D5, 0x99F50599, 0xA5DD11A5, 0x9F099559, 0xAD1A5D15,
0x8E4D9655, 0x8E964D55, 0x9F950959, 0xAD5D1A15, 0xB2719655, 0xB2967155, 0xB7219565, 0xB9267515,
0xB9752615, 0xB7952165, 0x9095F959, 0xA151DAD5, 0x8495ED65, 0x8945E6D5, 0x9905F599, 0xA511DDA5,
0x3FA3C50C, 0x5FC5A30A, 0x3F8BD130, 0x77D18B22, 0x77B18D44, 0x5F8DB150, 0x3AF3C05C, 0x5CF5A03A,
0x38FBD310, 0x7D7182B2, 0x7B7184D4, 0x58FDB510, 0x2CEFC704, 0x7D4D828E, 0x2ECFC074, 0x74DD882E,
0x64FD9D04, 0x6F4D90D4, 0x7B2B848E, 0x4AEFA702, 0x6F2B90B2, 0x62FB9B02, 0x72BB884E, 0x4EAFA072,
0x3FC5A30C, 0x5FA3C50A, 0x3FD18B30, 0x778BD122, 0x778DB144, 0x5FB18D50, 0x3AC0F35C, 0x5CA0F53A,
0x38D3FB10, 0x7D8271B2, 0x7B8471D4, 0x58B5FD10, 0x2CC7EF04, 0x7D824D8E, 0x2EC0CF74, 0x7488DD2E,
0x649DFD04, 0x6F904DD4, 0x7B842B8E, 0x4AA7EF02, 0x6F902BB2, 0x629BFB02, 0x7288BB4E, 0x4EA0AF72,
0x3CA0F53C, 0x5AC0F35A, 0x3D83F1B0, 0x78D27B12, 0x78B47D14, 0x5B85F1D0, 0x3CF5A03C, 0x5AF3C05A,
0x3DF183B0, 0x787BD212, 0x787DB414, 0x5BF185D0, 0x2CE0C7F4, 0x7848D2DE, 0x2CC7E0F4, 0x78D248DE,
0x69F04DD4, 0x694DF0D4, 0x7828B4BE, 0x4AE0A7F2, 0x692BF0B2, 0x69F02BB2, 0x78B428BE, 0x4AA7E0F2,
0x3D83CD8C, 0x6CC66F06, 0x3C88DD3C, 0x66C0CF66, 0x6791CDC4, 0x6C9C7D14, 0x38D3C8DC, 0x6CC660F6,
0x38C8D3DC, 0x6C60C6F6, 0x6971CCD4, 0x69CC71D4, 0x3DCD838C, 0x6C6FC606, 0x3CDD883C, 0x66CFC066,
0x67CD91C4, 0x6C7D9C14, 0x692BCC8E, 0x69CC2B8E, 0x6C289CBE, 0x62C89BCE, 0x629BC8CE, 0x6C9C28BE,
0x6AA66F06, 0x5B85AB8A, 0x6A9A7B12, 0x6791ABA2, 0x66A0AF66, 0x5A88BB5A, 0x6AA660F6, 0x58B5A8BA,
0x69AA71B2, 0x6971AAB2, 0x6A60A6F6, 0x58A8B5BA, 0x69AA4D8E, 0x694DAA8E, 0x6A9A48DE, 0x649DA8AE,
0x64A89DAE, 0x6A489ADE, 0x6A6FA606, 0x5BAB858A, 0x6A7B9A12, 0x67AB91A2, 0x66AFA066, 0x5ABB885A,
0xC05C3AF3, 0xA03A5CF5, 0xC0742ECF, 0x882E74DD, 0x884E72BB, 0xA0724EAF, 0xC50C3FA3, 0xA30A5FC5,
0xC7042CEF, 0x828E7D4D, 0x848E7B2B, 0xA7024AEF, 0xD31038FB, 0x82B27D71, 0xD1303F8B, 0x8B2277D1,
0x9B0262FB, 0x90B26F2B, 0x84D47B71, 0xB51058FD, 0x90D46F4D, 0x9D0464FD, 0x8D4477B1, 0xB1505F8D,
0xC03A5CF3, 0xA05C3AF5, 0xC02E74CF, 0x88742EDD, 0x88724EBB, 0xA04E72AF, 0xC53F0CA3, 0xA35F0AC5,
0xC72C04EF, 0x827D8E4D, 0x847B8E2B, 0xA74A02EF, 0xD33810FB, 0x827DB271, 0xD13F308B, 0x8B7722D1,
0x9B6202FB, 0x906FB22B, 0x847BD471, 0xB55810FD, 0x906FD44D, 0x9D6404FD, 0x8D7744B1, 0xB15F508D,
0xC35F0AC3, 0xA53F0CA5, 0xC27C0E4F, 0x872D84ED, 0x874B82EB, 0xA47A0E2F, 0xC30A5FC3, 0xA50C3FA5,
0xC20E7C4F, 0x87842DED, 0x87824BEB, 0xA40E7A2F, 0xD31F380B, 0x87B72D21, 0xD3381F0B, 0x872DB721,
0x960FB22B, 0x96B20F2B, 0x87D74B41, 0xB51F580D, 0x96D40F4D, 0x960FD44D, 0x874BD741, 0xB5581F0D,
0xC27C3273, 0x933990F9, 0xC37722C3, 0x993F3099, 0x986E323B, 0x936382EB, 0xC72C3723, 0x93399F09,
0xC7372C23, 0x939F3909, 0x968E332B, 0x96338E2B, 0xC2327C73, 0x939039F9, 0xC32277C3, 0x99303F99,
0x98326E3B, 0x938263EB, 0x96D43371, 0x9633D471, 0x93D76341, 0x9D376431, 0x9D643731, 0x9363D741,
0x955990F9, 0xA47A5475, 0x956584ED, 0x986E545D, 0x995F5099, 0xA57744A5, 0x95599F09, 0xA74A5745,
0x96558E4D, 0x968E554D, 0x959F5909, 0xA7574A45, 0x9655B271, 0x96B25571, 0x9565B721, 0x9B625751,
0x9B576251, 0x95B76521, 0x959059F9, 0xA4547A75, 0x958465ED, 0x98546E5D, 0x99505F99, 0xA54477A5,
0xCF5C3A03, 0xAF3A5C05, 0xF3742E03, 0xBB2E7411, 0xDD4E7211, 0xF5724E05, 0xC5FC30A3, 0xA3FA50C5,
0xF73420E3, 0xB2BE7141, 0xD4DE7121, 0xF75240E5, 0xDF1C08CB, 0x8EBE4D41, 0xD1FC0C8B, 0x8BEE44D1,
0xDF4640D9, 0xD4F64D09, 0x8EDE2B21, 0xBF1A08AD, 0xB2F62B09, 0xBF2620B9, 0x8DEE22B1, 0xB1FA0A8D,
0xCF3A5C03, 0xAF5C3A05, 0xF32E7403, 0xBB742E11, 0xDD724E11, 0xF54E7205, 0xC530FCA3, 0xA350FAC5,
0xF72034E3, 0xB271BE41, 0xD471DE21, 0xF74052E5, 0xDF081CCB, 0x8E4DBE41, 0xD10CFC8B, 0x8B44EED1,
0xDF4046D9, 0xD44DF609, 0x8E2BDE21, 0xBF081AAD, 0xB22BF609, 0xBF2026B9, 0x8D22EEB1, 0xB10AFA8D,
0xC350FAC3, 0xA530FCA5, 0xF2703E43, 0xB721B4E1, 0xD741D2E1, 0xF4705E25, 0xC3FA50C3, 0xA5FC30A5,
0xF23E7043, 0xB7B421E1, 0xD7D241E1, 0xF45E7025, 0xD01CF8CB, 0x84B4EDE1, 0xD0F81CCB, 0x84EDB4E1,
0xD44DF069, 0xD4F04D69, 0x82D2EBE1, 0xB01AF8AD, 0xB2F02B69, 0xB22BF069, 0x82EBD2E1, 0xB0F81AAD,
0xCE4C3E43, 0x9F099CC9, 0xC344EEC3, 0x990CFC99, 0xDC4C7619, 0xD741C6C9, 0xC4EC34E3, 0x90F99CC9,
0xC434ECE3, 0x909CF9C9, 0xD4CC7169, 0xD471CC69, 0xCE3E4C43, 0x9F9C09C9, 0xC3EE44C3, 0x99FC0C99,
0xDC764C19, 0xD7C641C9, 0x8ECC2B69, 0x8E2BCC69, 0x82C6EBC9, 0x8C26ECB9, 0x8CEC26B9, 0x82EBC6C9,
0x9F099AA9, 0xAE2A5E25, 0xB721A6A9, 0xBA2A7619, 0x990AFA99, 0xA522EEA5, 0x90F99AA9, 0xA2EA52E5,
0xB271AA69, 0xB2AA7169, 0x909AF9A9, 0xA252EAE5, 0x8E4DAA69, 0x8EAA4D69, 0x84EDA6A9, 0x8AEA46D9,
0x8A46EAD9, 0x84A6EDA9, 0x9F9A09A9, 0xAE5E2A25, 0xB7A621A9, 0xBA762A19, 0x99FA0A99, 0xA5EE22A5,
0x30A3C5FC, 0x50C5A3FA, 0x0C8BD1FC, 0x44D18BEE, 0x22B18DEE, 0x0A8DB1FA, 0x3A03CF5C, 0x5C05AF3A,
0x08CBDF1C, 0x4D418EBE, 0x2B218EDE, 0x08ADBF1A, 0x20E3F734, 0x7141B2BE, 0x2E03F374, 0x7411BB2E,
0x20B9BF26, 0x2B09B2F6, 0x7121D4DE, 0x40E5F752, 0x4D09D4F6, 0x40D9DF46, 0x7211DD4E, 0x4E05F572,
0x30C5A3FC, 0x50A3C5FA, 0x0CD18BFC, 0x448BD1EE, 0x228DB1EE, 0x0AB18DFA, 0x3ACF035C, 0x5CAF053A,
0x08DFCB1C, 0x4D8E41BE, 0x2B8E21DE, 0x08BFAD1A, 0x20F7E334, 0x71B241BE, 0x2EF30374, 0x74BB112E,
0x20BFB926, 0x2BB209F6, 0x71D421DE, 0x40F7E552, 0x4DD409F6, 0x40DFD946, 0x72DD114E, 0x4EF50572,
0x3CAF053C, 0x5ACF035A, 0x0D8FC1BC, 0x48DE4B1E, 0x28BE2D1E, 0x0B8FA1DA, 0x3C05AF3C, 0x5A03CF5A,
0x0DC18FBC, 0x484BDE1E, 0x282DBE1E, 0x0BA18FDA, 0x2FE30734, 0x7B4B121E, 0x2F07E334, 0x7B124B1E,
0x2BB20F96, 0x2B0FB296, 0x7D2D141E, 0x4FE50752, 0x4D0FD496, 0x4DD40F96, 0x7D142D1E, 0x4F07E552,
0x31B3C1BC, 0x60F66336, 0x3CBB113C, 0x66F30366, 0x23B389E6, 0x28BE3936, 0x3B13CB1C, 0x6F066336,
0x3BCB131C, 0x6F630636, 0x2B338E96, 0x2B8E3396, 0x31C1B3BC, 0x6063F636, 0x3C11BB3C, 0x6603F366,
0x2389B3E6, 0x2839BE36, 0x7133D496, 0x71D43396, 0x7D391436, 0x73D91346, 0x7313D946, 0x7D143936,
0x60F66556, 0x51D5A1DA, 0x48DE5956, 0x45D589E6, 0x66F50566, 0x5ADD115A, 0x6F066556, 0x5D15AD1A,
0x4D8E5596, 0x4D558E96, 0x6F650656, 0x5DAD151A, 0x71B25596, 0x7155B296, 0x7B125956, 0x7515B926,
0x75B91526, 0x7B591256, 0x6065F656, 0x51A1D5DA, 0x4859DE56, 0x4589D5E6, 0x6605F566, 0x5A11DD5A,
0xCFAC3503, 0xAFCA5305, 0xF3B81D03, 0xBBE24711, 0xDDE42711, 0xF5D81B05, 0xCAFC3053, 0xACFA5035,
0xFB3810D3, 0xBEB24171, 0xDED42171, 0xFD5810B5, 0xEF2C04C7, 0xBE8E414D, 0xE2FC0C47, 0xB8EE441D,
0xFD64049D, 0xF6D4094D, 0xDE8E212B, 0xEF4A02A7, 0xF6B2092B, 0xFB62029B, 0xD8EE221B, 0xE4FA0A27,
0xCF35AC03, 0xAF53CA05, 0xF31DB803, 0xBB47E211, 0xDD27E411, 0xF51BD805, 0xCA30FC53, 0xAC50FA35,
0xFB1038D3, 0xBE41B271, 0xDE21D471, 0xFD1058B5, 0xEF042CC7, 0xBE418E4D, 0xE20CFC47, 0xB844EE1D,
0xFD04649D, 0xF609D44D, 0xDE218E2B, 0xEF024AA7, 0xF609B22B, 0xFB02629B, 0xD822EE1B, 0xE40AFA27,
0xC3A0F5C3, 0xA5C0F3A5, 0xF1B03D83, 0xB4E1B721, 0xD2E1D741, 0xF1D05B85, 0xC3F5A0C3, 0xA5F3C0A5,
0xF13DB083, 0xB4B7E121, 0xD2D7E141, 0xF15BD085, 0xE02CF4C7, 0xB484E1ED, 0xE0F42CC7, 0xB4E184ED,
0xF069D44D, 0xF0D4694D, 0xD282E1EB, 0xE04AF2A7, 0xF0B2692B, 0xF069B22B, 0xD2E182EB, 0xE0F24AA7,
0xCD8C3D83, 0x9CC99F09, 0xC388DDC3, 0x99C0CF99, 0xCDC46791, 0xC6C9D741, 0xC8DC38D3, 0x9CC990F9,
0xC838DCD3, 0x9C90C9F9, 0xCCD46971, 0xCC69D471, 0xCD3D8C83, 0x9C9FC909, 0xC3DD88C3, 0x99CFC099,
0xCD67C491, 0xC6D7C941, 0xCC8E692B, 0xCC698E2B, 0xC682C9EB, 0xC862CE9B, 0xC8CE629B, 0xC6C982EB,
0x9AA99F09, 0xAB8A5B85, 0xA6A9B721, 0xABA26791, 0x99A0AF99, 0xA588BBA5, 0x9AA990F9, 0xA8BA58B5,
0xAA69B271, 0xAAB26971, 0x9A90A9F9, 0xA858BAB5, 0xAA698E4D, 0xAA8E694D, 0xA6A984ED, 0xA8AE649D,
0xA864AE9D, 0xA684A9ED, 0x9A9FA909, 0xAB5B8A85, 0xA6B7A921, 0xAB67A291, 0x99AFA099, 0xA5BB88A5,
0x3053CAFC, 0x5035ACFA, 0x0C47E2FC, 0x441DB8EE, 0x221BD8EE, 0x0A27E4FA, 0x3503CFAC, 0x5305AFCA,
0x04C7EF2C, 0x414DBE8E, 0x212BDE8E, 0x02A7EF4A, 0x10D3FB38, 0x4171BEB2, 0x1D03F3B8, 0x4711BBE2,
0x029BFB62, 0x092BF6B2, 0x2171DED4, 0x10B5FD58, 0x094DF6D4, 0x049DFD64, 0x2711DDE4, 0x1B05F5D8,
0x30CA53FC, 0x50AC35FA, 0x0CE247FC, 0x44B81DEE, 0x22D81BEE, 0x0AE427FA, 0x35CF03AC, 0x53AF05CA,
0x04EFC72C, 0x41BE4D8E, 0x21DE2B8E, 0x02EFA74A, 0x10FBD338, 0x41BE71B2, 0x1DF303B8, 0x47BB11E2,
0x02FB9B62, 0x09F62BB2, 0x21DE71D4, 0x10FDB558, 0x09F64DD4, 0x04FD9D64, 0x27DD11E4, 0x1BF505D8,
0x3C5F0A3C, 0x5A3F0C5A, 0x0E4FC27C, 0x4B1E48DE, 0x2D1E28BE, 0x0E2FA47A, 0x3C0A5F3C, 0x5A0C3F5A,
0x0EC24F7C, 0x4B481EDE, 0x2D281EBE, 0x0EA42F7A, 0x1FD30B38, 0x4B7B1E12, 0x1F0BD338, 0x4B1E7B12,
0x0F962BB2, 0x0F2B96B2, 0x2D7D1E14, 0x1FB50D58, 0x0F4D96D4, 0x0F964DD4, 0x2D1E7D14, 0x1F0DB558,
0x3273C27C, 0x633660F6, 0x3C77223C, 0x663F3066, 0x323B986E, 0x393628BE, 0x3723C72C, 0x63366F06,
0x37C7232C, 0x636F3606, 0x332B968E, 0x33962B8E, 0x32C2737C, 0x636036F6, 0x3C22773C, 0x66303F66,
0x32983B6E, 0x392836BE, 0x337196D4, 0x339671D4, 0x397D3614, 0x379D3164, 0x37319D64, 0x39367D14,
0x655660F6, 0x5475A47A, 0x595648DE, 0x545D986E, 0x665F5066, 0x5A77445A, 0x65566F06, 0x5745A74A,
0x55964D8E, 0x554D968E, 0x656F5606, 0x57A7454A, 0x559671B2, 0x557196B2, 0x59567B12, 0x57519B62,
0x579B5162, 0x597B5612, 0x656056F6, 0x54A4757A, 0x594856DE, 0x54985D6E, 0x66505F66, 0x5A44775A,
0x533F0CCA, 0x355F0AAC, 0x473F30E2, 0x1D7722B8, 0x1B7744D8, 0x275F50E4, 0x437F3E02, 0x17D72B28,
0x17B74D48, 0x257F5E04, 0x197F7610, 0x179F7160, 0x530C3FCA, 0x350A5FAC, 0x47303FE2, 0x1D2277B8,
0x1B4477D8, 0x27505FE4, 0x433E7F02, 0x172BD728, 0x174DB748, 0x255E7F04, 0x19767F10, 0x17719F60,
0x503C3CFA, 0x305A5AFC, 0x433E70F2, 0x127BD278, 0x147DB478, 0x255E70F4, 0x43703EF2, 0x12D27B78,
0x14B47D78, 0x25705EF4, 0x177196F0, 0x179671F0, 0x433E4CCE, 0x066FC66C, 0x443C3CEE, 0x0C6666FC,
0x19764CDC, 0x147D9C6C, 0x434C3ECE, 0x06C66F6C, 0x17964DCC, 0x174D96CC, 0x194C76DC, 0x149C7D6C,
0x066FA66A, 0x255E2AAE, 0x127B9A6A, 0x19762ABA, 0x0A6666FA, 0x225A5AEE, 0x172B96AA, 0x17962BAA,
0x06A66F6A, 0x252A5EAE, 0x192A76BA, 0x129A7B6A, 0xACC0F335, 0xCAA0F553, 0xB8C0CF1D, 0xE288DD47,
0xE488BB27, 0xD8A0AF1B, 0xBC80C1FD, 0xE828D4D7, 0xE848B2B7, 0xDA80A1FB, 0xE68089EF, 0xE8608E9F,
0xACF3C035, 0xCAF5A053, 0xB8CFC01D, 0xE2DD8847, 0xE4BB8827, 0xD8AFA01B, 0xBCC180FD, 0xE8D428D7,
0xE8B248B7, 0xDAA180FB, 0xE68980EF, 0xE88E609F, 0xAFC3C305, 0xCFA5A503, 0xBCC18F0D, 0xED842D87,
0xEB824B87, 0xDAA18F0B, 0xBC8FC10D, 0xED2D8487, 0xEB4B8287, 0xDA8FA10B, 0xE88E690F, 0xE8698E0F,
0xBCC1B331, 0xF9903993, 0xBBC3C311, 0xF3999903, 0xE689B323, 0xEB826393, 0xBCB3C131, 0xF9399093,
0xE869B233, 0xE8B26933, 0xE6B38923, 0xEB638293, 0xF9905995, 0xDAA1D551, 0xED846595, 0xE689D545,
0xF5999905, 0xDDA5A511, 0xE8D46955, 0xE869D455, 0xF9599095, 0xDAD5A151, 0xE6D58945, 0xED658495,
0xA33F0CC5, 0xC55F0AA3, 0x8B3F30D1, 0xD177228B, 0xB177448D, 0x8D5F50B1, 0x83BF3D01, 0xD717282B,
0xB717484D, 0x85DF5B01, 0x91F76701, 0x9F176071, 0xA30C3FC5, 0xC50A5FA3, 0x8B303FD1, 0xD122778B,
0xB144778D, 0x8D505FB1, 0x833DBF01, 0xD728172B, 0xB748174D, 0x855BDF01, 0x9167F701, 0x9F601771,
0xA03C3CF5, 0xC05A5AF3, 0x833DB0F1, 0xD278127B, 0xB478147D, 0x855BD0F1, 0x83B03DF1, 0xD212787B,
0xB414787D, 0x85D05BF1, 0x96F01771, 0x9617F071, 0x833D8CCD, 0xC66C066F, 0x883C3CDD, 0xC06666CF,
0x9167C4CD, 0x9C6C147D, 0x838C3DCD, 0xC6066C6F, 0x9617CC4D, 0x96CC174D, 0x91C467CD, 0x9C146C7D,
0xA66A066F, 0x855B8AAB, 0x9A6A127B, 0x9167A2AB, 0xA06666AF, 0x885A5ABB, 0x96AA172B, 0x9617AA2B,
0xA6066A6F, 0x858A5BAB, 0x91A267AB, 0x9A126A7B, 0x5CC0F33A, 0x3AA0F55C, 0x74C0CF2E, 0x2E88DD74,
0x4E88BB72, 0x72A0AF4E, 0x7C40C2FE, 0x28E8D7D4, 0x48E8B7B2, 0x7A20A4FE, 0x6E0898FE, 0x60E89F8E,
0x5CF3C03A, 0x3AF5A05C, 0x74CFC02E, 0x2EDD8874, 0x4EBB8872, 0x72AFA04E, 0x7CC240FE, 0x28D7E8D4,
0x48B7E8B2, 0x7AA420FE, 0x6E9808FE, 0x609FE88E, 0x5FC3C30A, 0x3FA5A50C, 0x7CC24F0E, 0x2D87ED84,
0x4B87EB82, 0x7AA42F0E, 0x7C4FC20E, 0x2DED8784, 0x4BEB8782, 0x7A2FA40E, 0x690FE88E, 0x69E80F8E,
0x7CC27332, 0x3993F990, 0x77C3C322, 0x3F999930, 0x6E983B32, 0x6393EB82, 0x7C73C232, 0x39F99390,
0x69E833B2, 0x6933E8B2, 0x6E3B9832, 0x63EB9382, 0x5995F990, 0x7AA47554, 0x6595ED84, 0x6E985D54,
0x5F999950, 0x77A5A544, 0x6955E8D4, 0x69E855D4, 0x59F99590, 0x7A75A454, 0x6E5D9854, 0x65ED9584,
0x5CCF033A, 0x3AAF055C, 0x74F3032E, 0x2EBB1174, 0x4EDD1172, 0x72F5054E, 0x7F43023E, 0x2BEB1714,
0x4DED1712, 0x7F25045E, 0x7F191076, 0x71F91706, 0x5C03CF3A, 0x3A05AF5C, 0x7403F32E, 0x2E11BB74,
0x4E11DD72, 0x7205F54E, 0x7F02433E, 0x2B17EB14, 0x4D17ED12, 0x7F04255E, 0x7F101976, 0x7117F906,
0x50C3C3FA, 0x30A5A5FC, 0x70F2433E, 0x21B7E1B4, 0x41D7E1D2, 0x70F4255E, 0x7043F23E, 0x21E1B7B4,
0x41E1D7D2, 0x7025F45E, 0x7117F096, 0x71F01796, 0x4CCE433E, 0x099FC99C, 0x44C3C3EE, 0x0C9999FC,
0x4CDC1976, 0x41D7C9C6, 0x4C43CE3E, 0x09C99F9C, 0x4DCC1796, 0x4D17CC96, 0x4C19DC76, 0x41C9D7C6,
0x099FA99A, 0x2AAE255E, 0x21B7A9A6, 0x2ABA1976, 0x0A9999FA, 0x22A5A5EE, 0x2B17AA96, 0x2BAA1796,
0x09A99F9A, 0x2A25AE5E, 0x2A19BA76, 0x21A9B7A6, 0xA330FCC5, 0xC550FAA3, 0x8B0CFCD1, 0xD144EE8B,
0xB122EE8D, 0x8D0AFAB1, 0x80BCFDC1, 0xD414E8EB, 0xB212E8ED, 0x80DAFBA1, 0x80E6EF89, 0x8E06E8F9,
0xA3FC30C5, 0xC5FA50A3, 0x8BFC0CD1, 0xD1EE448B, 0xB1EE228D, 0x8DFA0AB1, 0x80FDBCC1, 0xD4E814EB,
0xB2E812ED, 0x80FBDAA1, 0x80EFE689, 0x8EE806F9, 0xAF3C3C05, 0xCF5A5A03, 0x8F0DBCC1, 0xDE481E4B,
0xBE281E2D, 0x8F0BDAA1, 0x8FBC0DC1, 0xDE1E484B, 0xBE1E282D, 0x8FDA0BA1, 0x8EE80F69, 0x8E0FE869,
0xB331BCC1, 0xF6603663, 0xBB3C3C11, 0xF3666603, 0xB323E689, 0xBE283639, 0xB3BC31C1, 0xF6366063,
0xB233E869, 0xB2E83369, 0xB3E62389, 0xBE362839, 0xF6605665, 0xD551DAA1, 0xDE485659, 0xD545E689,
0xF5666605, 0xDD5A5A11, 0xD4E85569, 0xD455E869, 0xF6566065, 0xD5DA51A1, 0xD5E64589, 0xDE564859,
0xACCF0335, 0xCAAF0553, 0xB8F3031D, 0xE2BB1147, 0xE4DD1127, 0xD8F5051B, 0xBF83013D, 0xEB2B1417,
0xED4D1217, 0xDF85015B, 0xF7910167, 0xF9710617, 0xAC03CF35, 0xCA05AF53, 0xB803F31D, 0xE211BB47,
0xE411DD27, 0xD805F51B, 0xBF01833D, 0xEB142B17, 0xED124D17, 0xDF01855B, 0xF7019167, 0xF9067117,
0xA0C3C3F5, 0xC0A5A5F3, 0xB0F1833D, 0xE1B421B7, 0xE1D241D7, 0xD0F1855B, 0xB083F13D, 0xE121B4B7,
0xE141D2D7, 0xD085F15B, 0xF0967117, 0xF0719617, 0x8CCD833D, 0xC99C099F, 0x88C3C3DD, 0xC09999CF,
0xC4CD9167, 0xC9C641D7, 0x8C83CD3D, 0xC9099C9F, 0xCC4D9617, 0xCC964D17, 0xC491CD67, 0xC941C6D7,
0xA99A099F, 0x8AAB855B, 0xA9A621B7, 0xA2AB9167, 0xA09999AF, 0x88A5A5BB, 0xAA962B17, 0xAA2B9617,
0xA9099A9F, 0x8A85AB5B, 0xA291AB67, 0xA921A6B7, 0x5330FCCA, 0x3550FAAC, 0x470CFCE2, 0x1D44EEB8,
0x1B22EED8, 0x270AFAE4, 0x407CFEC2, 0x14D4EBE8, 0x12B2EDE8, 0x207AFEA4, 0x086EFE98, 0x068EF9E8,
0x53FC30CA, 0x35FA50AC, 0x47FC0CE2, 0x1DEE44B8, 0x1BEE22D8, 0x27FA0AE4, 0x40FE7CC2, 0x14EBD4E8,
0x12EDB2E8, 0x20FE7AA4, 0x08FE6E98, 0x06F98EE8, 0x5F3C3C0A, 0x3F5A5A0C, 0x4F0E7CC2, 0x1E4BDE48,
0x1E2DBE28, 0x2F0E7AA4, 0x4F7C0EC2, 0x1EDE4B48, 0x1EBE2D28, 0x2F7A0EA4, 0x0F698EE8, 0x0F8E69E8,
0x73327CC2, 0x3663F660, 0x773C3C22, 0x3F666630, 0x3B326E98, 0x3639BE28, 0x737C32C2, 0x36F66360,
0x33B269E8, 0x3369B2E8, 0x3B6E3298, 0x36BE3928, 0x5665F660, 0x75547AA4, 0x5659DE48, 0x5D546E98,
0x5F666650, 0x775A5A44, 0x5569D4E8, 0x55D469E8, 0x56F66560, 0x757A54A4, 0x5D6E5498, 0x56DE5948
};

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define SDB_MAX_CUTSIZE    6
#define SDB_MAX_CUTNUM     51
#define SDB_MAX_TT_WORDS   ((SDB_MAX_CUTSIZE > 6) ? 1 << (SDB_MAX_CUTSIZE-6) : 1)

#define SDB_CUT_NO_LEAF   0xF

typedef struct Sdb_Cut_t_ Sdb_Cut_t; 
struct Sdb_Cut_t_
{
    word            Sign;                      // signature
    int             iFunc;                     // functionality
    int             Cost;                      // cut cost
    int             CostLev;                   // cut cost
    unsigned        nTreeLeaves  : 28;         // tree leaves
    unsigned        nLeaves      :  4;         // leaf count
    int             pLeaves[SDB_MAX_CUTSIZE];  // leaves
};

typedef struct Sdb_Sto_t_ Sdb_Sto_t; 
struct Sdb_Sto_t_
{
    int             nCutSize;
    int             nCutNum;
    int             fCutMin;
    int             fVerbose;
    Gia_Man_t *     pGia;                      // user's AIG manager (will be modified by adding nodes)
    Vec_Int_t *     vRefs;                     // refs for each node
    Vec_Wec_t *     vCuts;                     // cuts for each node
    Vec_Mem_t *     vTtMem;                    // truth tables
    Sdb_Cut_t       pCuts[3][SDB_MAX_CUTNUM];  // temporary cuts
    Sdb_Cut_t *     ppCuts[SDB_MAX_CUTNUM];    // temporary cut pointers
    int             nCutsR;                    // the number of cuts
    int             Pivot;                     // current object
    int             iCutBest;                  // best-delay cut
    int             nCutsOver;                 // overflow cuts
    double          CutCount[4];               // cut counters
    abctime         clkStart;                  // starting time
};

static inline word * Sdb_CutTruth( Sdb_Sto_t * p, Sdb_Cut_t * pCut ) { return Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut->iFunc));           }

#define Sdb_ForEachCut( pList, pCut, i ) for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += pCut[0] + 2 )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Check correctness of cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Sdb_CutGetSign( Sdb_Cut_t * pCut )
{
    word Sign = 0; int i; 
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        Sign |= ((word)1) << (pCut->pLeaves[i] & 0x3F);
    return Sign;
}
static inline int Sdb_CutCheck( Sdb_Cut_t * pBase, Sdb_Cut_t * pCut ) // check if pCut is contained in pBase
{
    int nSizeB = pBase->nLeaves;
    int nSizeC = pCut->nLeaves;
    int i, * pB = pBase->pLeaves;
    int k, * pC = pCut->pLeaves;
    for ( i = 0; i < nSizeC; i++ )
    {
        for ( k = 0; k < nSizeB; k++ )
            if ( pC[i] == pB[k] )
                break;
        if ( k == nSizeB )
            return 0;
    }
    return 1;
}
static inline int Sdb_CutSetCheckArray( Sdb_Cut_t ** ppCuts, int nCuts )
{
    Sdb_Cut_t * pCut0, * pCut1; 
    int i, k, m, n, Value;
    assert( nCuts > 0 );
    for ( i = 0; i < nCuts; i++ )
    {
        pCut0 = ppCuts[i];
        assert( pCut0->nLeaves <= SDB_MAX_CUTSIZE );
        assert( pCut0->Sign == Sdb_CutGetSign(pCut0) );
        // check duplicates
        for ( m = 0; m < (int)pCut0->nLeaves; m++ )
        for ( n = m + 1; n < (int)pCut0->nLeaves; n++ )
            assert( pCut0->pLeaves[m] < pCut0->pLeaves[n] );
        // check pairs
        for ( k = 0; k < nCuts; k++ )
        {
            pCut1 = ppCuts[k];
            if ( pCut0 == pCut1 )
                continue;
            // check containments
            Value = Sdb_CutCheck( pCut0, pCut1 );
            assert( Value == 0 );
        }
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sdb_CutMergeOrder( Sdb_Cut_t * pCut0, Sdb_Cut_t * pCut1, Sdb_Cut_t * pCut, int nCutSize )
{ 
    int nSize0   = pCut0->nLeaves;
    int nSize1   = pCut1->nLeaves;
    int i, * pC0 = pCut0->pLeaves;
    int k, * pC1 = pCut1->pLeaves;
    int c, * pC  = pCut->pLeaves;
    // the case of the largest cut sizes
    if ( nSize0 == nCutSize && nSize1 == nCutSize )
    {
        for ( i = 0; i < nSize0; i++ )
        {
            if ( pC0[i] != pC1[i] )  return 0;
            pC[i] = pC0[i];
        }
        pCut->nLeaves = nCutSize;
        pCut->iFunc = -1;
        pCut->Sign = pCut0->Sign | pCut1->Sign;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = 0;
    if ( nSize0 == 0 ) goto FlushCut1;
    if ( nSize1 == 0 ) goto FlushCut0;
    while ( 1 )
    {
        if ( c == nCutSize ) return 0;
        if ( pC0[i] < pC1[k] )
        {
            pC[c++] = pC0[i++];
            if ( i >= nSize0 ) goto FlushCut1;
        }
        else if ( pC0[i] > pC1[k] )
        {
            pC[c++] = pC1[k++];
            if ( k >= nSize1 ) goto FlushCut0;
        }
        else
        {
            pC[c++] = pC0[i++]; k++;
            if ( i >= nSize0 ) goto FlushCut1;
            if ( k >= nSize1 ) goto FlushCut0;
        }
    }

FlushCut0:
    if ( c + nSize0 > nCutSize + i ) return 0;
    while ( i < nSize0 )
        pC[c++] = pC0[i++];
    pCut->nLeaves = c;
    pCut->iFunc = -1;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;

FlushCut1:
    if ( c + nSize1 > nCutSize + k ) return 0;
    while ( k < nSize1 )
        pC[c++] = pC1[k++];
    pCut->nLeaves = c;
    pCut->iFunc = -1;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;
}
static inline int Sdb_CutMergeOrder2( Sdb_Cut_t * pCut0, Sdb_Cut_t * pCut1, Sdb_Cut_t * pCut, int nCutSize )
{ 
    int x0, i0 = 0, nSize0 = pCut0->nLeaves, * pC0 = pCut0->pLeaves;
    int x1, i1 = 0, nSize1 = pCut1->nLeaves, * pC1 = pCut1->pLeaves;
    int xMin, c = 0, * pC  = pCut->pLeaves;
    while ( 1 )
    {
        x0 = (i0 == nSize0) ? ABC_INFINITY : pC0[i0];
        x1 = (i1 == nSize1) ? ABC_INFINITY : pC1[i1];
        xMin = Abc_MinInt(x0, x1);
        if ( xMin == ABC_INFINITY ) break;
        if ( c == nCutSize ) return 0;
        pC[c++] = xMin;
        if (x0 == xMin) i0++;
        if (x1 == xMin) i1++;
    }
    pCut->nLeaves = c;
    pCut->iFunc = -1;
    pCut->Sign = pCut0->Sign | pCut1->Sign;
    return 1;
}
static inline int Sdb_CutSetCutIsContainedOrder( Sdb_Cut_t * pBase, Sdb_Cut_t * pCut ) // check if pCut is contained in pBase
{
    int i, nSizeB = pBase->nLeaves;
    int k, nSizeC = pCut->nLeaves;
    if ( nSizeB == nSizeC )
    {
        for ( i = 0; i < nSizeB; i++ )
            if ( pBase->pLeaves[i] != pCut->pLeaves[i] )
                return 0;
        return 1;
    }
    assert( nSizeB > nSizeC ); 
    if ( nSizeC == 0 )
        return 1;
    for ( i = k = 0; i < nSizeB; i++ )
    {
        if ( pBase->pLeaves[i] > pCut->pLeaves[k] )
            return 0;
        if ( pBase->pLeaves[i] == pCut->pLeaves[k] )
        {
            if ( ++k == nSizeC )
                return 1;
        }
    }
    return 0;
}
static inline int Sdb_CutSetLastCutIsContained( Sdb_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[i]->nLeaves <= pCuts[nCuts]->nLeaves && (pCuts[i]->Sign & pCuts[nCuts]->Sign) == pCuts[i]->Sign && Sdb_CutSetCutIsContainedOrder(pCuts[nCuts], pCuts[i]) )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sdb_CutCompare( Sdb_Cut_t * pCut0, Sdb_Cut_t * pCut1 )
{
    if ( pCut0->nTreeLeaves < pCut1->nTreeLeaves )  return -1;
    if ( pCut0->nTreeLeaves > pCut1->nTreeLeaves )  return  1;
    if ( pCut0->nLeaves     < pCut1->nLeaves )      return -1;
    if ( pCut0->nLeaves     > pCut1->nLeaves )      return  1;
    return 0;
}
static inline int Sdb_CutSetLastCutContains( Sdb_Cut_t ** pCuts, int nCuts )
{
    int i, k, fChanges = 0;
    for ( i = 0; i < nCuts; i++ )
        if ( pCuts[nCuts]->nLeaves < pCuts[i]->nLeaves && (pCuts[nCuts]->Sign & pCuts[i]->Sign) == pCuts[nCuts]->Sign && Sdb_CutSetCutIsContainedOrder(pCuts[i], pCuts[nCuts]) )
            pCuts[i]->nLeaves = SDB_CUT_NO_LEAF, fChanges = 1;
    if ( !fChanges )
        return nCuts;
    for ( i = k = 0; i <= nCuts; i++ )
    {
        if ( pCuts[i]->nLeaves == SDB_CUT_NO_LEAF )
            continue;
        if ( k < i )
            ABC_SWAP( Sdb_Cut_t *, pCuts[k], pCuts[i] );
        k++;
    }
    return k - 1;
}
static inline void Sdb_CutSetSortByCost( Sdb_Cut_t ** pCuts, int nCuts )
{
    int i;
    for ( i = nCuts; i > 0; i-- )
    {
        if ( Sdb_CutCompare(pCuts[i - 1], pCuts[i]) < 0 )//!= 1 )
            return;
        ABC_SWAP( Sdb_Cut_t *, pCuts[i - 1], pCuts[i] );
    }
}
static inline int Sdb_CutSetAddCut( Sdb_Cut_t ** pCuts, int nCuts, int nCutNum )
{
    if ( nCuts == 0 )
        return 1;
    nCuts = Sdb_CutSetLastCutContains(pCuts, nCuts);
    assert( nCuts >= 0 );
    Sdb_CutSetSortByCost( pCuts, nCuts );
    // add new cut if there is room
    return Abc_MinInt( nCuts + 1, nCutNum - 1 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sdb_CutComputeTruth6( Sdb_Sto_t * p, Sdb_Cut_t * pCut0, Sdb_Cut_t * pCut1, int fCompl0, int fCompl1, Sdb_Cut_t * pCutR, int fIsXor )
{
    int nOldSupp = pCutR->nLeaves, truthId, fCompl; word t;
    word t0 = *Sdb_CutTruth(p, pCut0);
    word t1 = *Sdb_CutTruth(p, pCut1);
    if ( Abc_LitIsCompl(pCut0->iFunc) ^ fCompl0 ) t0 = ~t0;
    if ( Abc_LitIsCompl(pCut1->iFunc) ^ fCompl1 ) t1 = ~t1;
    t0 = Abc_Tt6Expand( t0, pCut0->pLeaves, pCut0->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t1 = Abc_Tt6Expand( t1, pCut1->pLeaves, pCut1->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    t =  fIsXor ? t0 ^ t1 : t0 & t1;
    if ( (fCompl = (int)(t & 1)) ) t = ~t;
    pCutR->nLeaves = Abc_Tt6MinBase( &t, pCutR->pLeaves, pCutR->nLeaves );
    assert( (int)(t & 1) == 0 );
    truthId        = Vec_MemHashInsert(p->vTtMem, &t);
    pCutR->iFunc   = Abc_Var2Lit( truthId, fCompl );
    assert( (int)pCutR->nLeaves <= nOldSupp );
    return (int)pCutR->nLeaves < nOldSupp;
}
static inline int Sdb_CutComputeTruth( Sdb_Sto_t * p, Sdb_Cut_t * pCut0, Sdb_Cut_t * pCut1, int fCompl0, int fCompl1, Sdb_Cut_t * pCutR, int fIsXor )
{
    if ( p->nCutSize <= 6 )
        return Sdb_CutComputeTruth6( p, pCut0, pCut1, fCompl0, fCompl1, pCutR, fIsXor );
    {
    word uTruth[SDB_MAX_TT_WORDS], uTruth0[SDB_MAX_TT_WORDS], uTruth1[SDB_MAX_TT_WORDS];
    int nOldSupp   = pCutR->nLeaves, truthId;
    int nCutSize   = p->nCutSize, fCompl;
    int nWords     = Abc_Truth6WordNum(nCutSize);
    word * pTruth0 = Sdb_CutTruth(p, pCut0);
    word * pTruth1 = Sdb_CutTruth(p, pCut1);
    Abc_TtCopy( uTruth0, pTruth0, nWords, Abc_LitIsCompl(pCut0->iFunc) ^ fCompl0 );
    Abc_TtCopy( uTruth1, pTruth1, nWords, Abc_LitIsCompl(pCut1->iFunc) ^ fCompl1 );
    Abc_TtExpand( uTruth0, nCutSize, pCut0->pLeaves, pCut0->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    Abc_TtExpand( uTruth1, nCutSize, pCut1->pLeaves, pCut1->nLeaves, pCutR->pLeaves, pCutR->nLeaves );
    if ( fIsXor )
        Abc_TtXor( uTruth, uTruth0, uTruth1, nWords, (fCompl = (int)((uTruth0[0] ^ uTruth1[0]) & 1)) );
    else
        Abc_TtAnd( uTruth, uTruth0, uTruth1, nWords, (fCompl = (int)((uTruth0[0] & uTruth1[0]) & 1)) );
    pCutR->nLeaves = Abc_TtMinBase( uTruth, pCutR->pLeaves, pCutR->nLeaves, nCutSize );
    assert( (uTruth[0] & 1) == 0 );
//Kit_DsdPrintFromTruth( uTruth, pCutR->nLeaves ), printf("\n" ), printf("\n" );
    truthId        = Vec_MemHashInsert(p->vTtMem, uTruth);
    pCutR->iFunc   = Abc_Var2Lit( truthId, fCompl );
    assert( (int)pCutR->nLeaves <= nOldSupp );
    return (int)pCutR->nLeaves < nOldSupp;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sdb_CutCountBits( word i )
{
    i = i - ((i >> 1) & 0x5555555555555555);
    i = (i & 0x3333333333333333) + ((i >> 2) & 0x3333333333333333);
    i = ((i + (i >> 4)) & 0x0F0F0F0F0F0F0F0F);
    return (i*(0x0101010101010101))>>56;
}
static inline void Sdb_CutAddUnit( Sdb_Sto_t * p, int iObj )
{
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    if ( Vec_IntSize(vThis) == 0 )
        Vec_IntPush( vThis, 1 );
    else 
        Vec_IntAddToEntry( vThis, 0, 1 );
    Vec_IntPush( vThis, 1 );
    Vec_IntPush( vThis, iObj );
    Vec_IntPush( vThis, 2 );
}
static inline void Sdb_CutAddZero( Sdb_Sto_t * p, int iObj )
{
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    assert( Vec_IntSize(vThis) == 0 );
    Vec_IntPush( vThis, 1 );
    Vec_IntPush( vThis, 0 );
    Vec_IntPush( vThis, 0 );
}
static inline int Sdb_CutTreeLeaves( Sdb_Sto_t * p, Sdb_Cut_t * pCut )
{
    int i, Cost = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        Cost += Vec_IntEntry( p->vRefs, pCut->pLeaves[i] ) == 1;
    return Cost;
}
static inline int Sdb_StoPrepareSet( Sdb_Sto_t * p, int iObj, int Index )
{
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    int i, v, * pCut, * pList = Vec_IntArray( vThis );
    Sdb_ForEachCut( pList, pCut, i )
    {
        Sdb_Cut_t * pCutTemp = &p->pCuts[Index][i];
        pCutTemp->nLeaves = pCut[0];
        for ( v = 1; v <= pCut[0]; v++ )
            pCutTemp->pLeaves[v-1] = pCut[v];
        pCutTemp->iFunc = pCut[pCut[0]+1];
        pCutTemp->Sign = Sdb_CutGetSign( pCutTemp );
        pCutTemp->nTreeLeaves = Sdb_CutTreeLeaves( p, pCutTemp );
    }
    return pList[0];
}
static inline void Sdb_StoInitResult( Sdb_Sto_t * p )
{
    int i; 
    for ( i = 0; i < SDB_MAX_CUTNUM; i++ )
        p->ppCuts[i] = &p->pCuts[2][i];
}
static inline void Sdb_StoStoreResult( Sdb_Sto_t * p, int iObj, Sdb_Cut_t ** pCuts, int nCuts )
{
    int i, v;
    Vec_Int_t * vList = Vec_WecEntry( p->vCuts, iObj );
    Vec_IntPush( vList, nCuts );
    for ( i = 0; i < nCuts; i++ )
    {
        Vec_IntPush( vList, pCuts[i]->nLeaves );
        for ( v = 0; v < (int)pCuts[i]->nLeaves; v++ )
            Vec_IntPush( vList, pCuts[i]->pLeaves[v] );
        Vec_IntPush( vList, pCuts[i]->iFunc );
    }
}
static inline void Sdb_CutPrint( Sdb_Sto_t * p, int iObj, Sdb_Cut_t * pCut )
{
    int i, nDigits = Abc_Base10Log(Gia_ManObjNum(p->pGia)); 
    if ( pCut == NULL ) { printf( "No cut.\n" ); return; }
    printf( "%d  {", pCut->nLeaves );
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
        printf( " %*d", nDigits, pCut->pLeaves[i] );
    for ( ; i < (int)p->nCutSize; i++ )
        printf( " %*s", nDigits, " " );
    printf( "  }  Cost = %3d  CostL = %3d  Tree = %d  ", 
        pCut->Cost, pCut->CostLev, pCut->nTreeLeaves );
    printf( "\n" );
}
void Sdb_StoMergeCuts( Sdb_Sto_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    int fIsXor       = Gia_ObjIsXor(pObj);
    int nCutSize     = p->nCutSize;
    int nCutNum      = p->nCutNum;
    int fComp0       = Gia_ObjFaninC0(pObj);
    int fComp1       = Gia_ObjFaninC1(pObj);
    int Fan0         = Gia_ObjFaninId0(pObj, iObj);
    int Fan1         = Gia_ObjFaninId1(pObj, iObj);
    int nCuts0       = Sdb_StoPrepareSet( p, Fan0, 0 );
    int nCuts1       = Sdb_StoPrepareSet( p, Fan1, 1 );
    int i, k, nCutsR = 0;
    Sdb_Cut_t * pCut0, * pCut1, ** pCutsR = p->ppCuts;
    assert( !Gia_ObjIsBuf(pObj) );
    assert( !Gia_ObjIsMux(p->pGia, pObj) );
    Sdb_StoInitResult( p );
    p->CutCount[0] += nCuts0 * nCuts1;
    for ( i = 0, pCut0 = p->pCuts[0]; i < nCuts0; i++, pCut0++ )
    for ( k = 0, pCut1 = p->pCuts[1]; k < nCuts1; k++, pCut1++ )
    {
        if ( (int)(pCut0->nLeaves + pCut1->nLeaves) > nCutSize && Sdb_CutCountBits(pCut0->Sign | pCut1->Sign) > nCutSize )
            continue;
        p->CutCount[1]++; 
        if ( !Sdb_CutMergeOrder(pCut0, pCut1, pCutsR[nCutsR], nCutSize) )
            continue;
        if ( Sdb_CutSetLastCutIsContained(pCutsR, nCutsR) )
            continue;
        p->CutCount[2]++;
        if ( p->fCutMin && Sdb_CutComputeTruth(p, pCut0, pCut1, fComp0, fComp1, pCutsR[nCutsR], fIsXor) )
            pCutsR[nCutsR]->Sign = Sdb_CutGetSign(pCutsR[nCutsR]);
        pCutsR[nCutsR]->nTreeLeaves = Sdb_CutTreeLeaves( p, pCutsR[nCutsR] );
        nCutsR = Sdb_CutSetAddCut( pCutsR, nCutsR, nCutNum );
    }
    p->CutCount[3] += nCutsR;
    p->nCutsOver += nCutsR == nCutNum-1;
    p->nCutsR = nCutsR;
    p->Pivot = iObj;
    // debug printout
    if ( 0 )
    {
        printf( "*** Obj = %4d  NumCuts = %4d\n", iObj, nCutsR );
        for ( i = 0; i < nCutsR; i++ )
            Sdb_CutPrint( p, iObj, pCutsR[i] );
        printf( "\n" );
    }
    // verify
    assert( nCutsR > 0 && nCutsR < nCutNum );
    assert( Sdb_CutSetCheckArray(pCutsR, nCutsR) );
    // store the cutset
    Sdb_StoStoreResult( p, iObj, pCutsR, nCutsR );
    if ( nCutsR > 1 || pCutsR[0]->nLeaves > 1 )
        Sdb_CutAddUnit( p, iObj );
}

/**Function*************************************************************

  Synopsis    [Iterate through the cuts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sdb_StoIterCutsOne( Sdb_Sto_t * p, int iObj )
{
    int fVerbose = 1;
    Vec_Int_t * vThis = Vec_WecEntry( p->vCuts, iObj );
    int i, k, * pCut, * pList = Vec_IntArray( vThis );
    word * pTruth;
    Sdb_ForEachCut( pList, pCut, i )
    {
        if ( pCut[0] != 5 )
            continue;
        pTruth = Vec_MemReadEntry(p->vTtMem, Abc_Lit2Var(pCut[pCut[0]+1]));
        for ( k = 0; k < 1920; k++ )
            if ( s_FuncTruths[k] == (unsigned)*pTruth )
                break;
        if ( k < 1920 )
        {
            if ( fVerbose )
            {
                printf( "Object %d has 5-input cut:  ", iObj );
                for ( k = 1; k <= pCut[0]; k++ )
                    printf( "%d ", pCut[k] );
                printf( "\n" );
            }
            return 1;
        }
    }
    return 0;
}
void Sdb_StoIterCuts( Sdb_Sto_t * p )
{
    Gia_Obj_t * pObj;   
    int iObj, Count = 0;
    Gia_ManForEachAnd( p->pGia, pObj, iObj )
        Count += Sdb_StoIterCutsOne( p, iObj );
    printf( "Detected %d cuts.\n", Count );
}

/**Function*************************************************************

  Synopsis    [Incremental cut computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sdb_Sto_t * Sdb_StoAlloc( Gia_Man_t * pGia, int nCutSize, int nCutNum, int fCutMin, int fVerbose )
{
    Sdb_Sto_t * p;
    assert( nCutSize < SDB_CUT_NO_LEAF );
    assert( nCutSize > 1 && nCutSize <= SDB_MAX_CUTSIZE );
    assert( nCutNum > 1 && nCutNum < SDB_MAX_CUTNUM );
    p = ABC_CALLOC( Sdb_Sto_t, 1 );
    p->clkStart = Abc_Clock();
    p->nCutSize = nCutSize;
    p->nCutNum  = nCutNum;
    p->fCutMin  = fCutMin;
    p->fVerbose = fVerbose;
    p->pGia     = pGia;
    p->vRefs    = Vec_IntAlloc( Gia_ManObjNum(pGia) );
    p->vCuts    = Vec_WecStart( Gia_ManObjNum(pGia) );
    p->vTtMem   = fCutMin ? Vec_MemAllocForTT( nCutSize, 0 ) : NULL;
    return p;
}
void Sdb_StoFree( Sdb_Sto_t * p )
{
    Vec_IntFree( p->vRefs );
    Vec_WecFree( p->vCuts );
    if ( p->fCutMin )
        Vec_MemHashFree( p->vTtMem );
    if ( p->fCutMin )
        Vec_MemFree( p->vTtMem );
    ABC_FREE( p );
}
void Sdb_StoComputeCutsConst0( Sdb_Sto_t * p, int iObj )
{
    Sdb_CutAddZero( p, iObj );
}
void Sdb_StoComputeCutsCi( Sdb_Sto_t * p, int iObj )
{
    Sdb_CutAddUnit( p, iObj );
}
void Sdb_StoComputeCutsNode( Sdb_Sto_t * p, int iObj )
{
    Sdb_StoMergeCuts( p, iObj );
}
void Sdb_StoRefObj( Sdb_Sto_t * p, int iObj )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, iObj);
    assert( iObj == Vec_IntSize(p->vRefs) );
    Vec_IntPush( p->vRefs, 0 );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Vec_IntAddToEntry( p->vRefs, Gia_ObjFaninId0(pObj, iObj), 1 );
        Vec_IntAddToEntry( p->vRefs, Gia_ObjFaninId1(pObj, iObj), 1 );
    }
    else if ( Gia_ObjIsCo(pObj) )
        Vec_IntAddToEntry( p->vRefs, Gia_ObjFaninId0(pObj, iObj), 1 );
}
void Sdb_StoComputeCutsTest( Gia_Man_t * pGia )
{
    Sdb_Sto_t * p = Sdb_StoAlloc( pGia, 6, 20, 1, 1 );
    Gia_Obj_t * pObj;   
    int i, iObj;
    // prepare references
    Gia_ManForEachObj( p->pGia, pObj, iObj )
        Sdb_StoRefObj( p, iObj );
    // compute cuts
    Sdb_StoComputeCutsConst0( p, 0 );
    Gia_ManForEachCiId( p->pGia, iObj, i )
        Sdb_StoComputeCutsCi( p, iObj );
    Gia_ManForEachAnd( p->pGia, pObj, iObj )
        Sdb_StoComputeCutsNode( p, iObj );
    if ( p->fVerbose )
    {
        printf( "Running cut computation with CutSize = %d  CutNum = %d:\n", p->nCutSize, p->nCutNum );
        printf( "CutPair = %.0f  ",         p->CutCount[0] );
        printf( "Merge = %.0f (%.2f %%)  ", p->CutCount[1], 100.0*p->CutCount[1]/p->CutCount[0] );
        printf( "Eval = %.0f (%.2f %%)  ",  p->CutCount[2], 100.0*p->CutCount[2]/p->CutCount[0] );
        printf( "Cut = %.0f (%.2f %%)  ",   p->CutCount[3], 100.0*p->CutCount[3]/p->CutCount[0] );
        printf( "Cut/Node = %.2f  ",        p->CutCount[3] / Gia_ManAndNum(p->pGia) );
        printf( "\n" );
        printf( "Over = %4d  ",             p->nCutsOver );
        Abc_PrintTime( 0, "Time", Abc_Clock() - p->clkStart );
    }
    Sdb_StoIterCuts( p );
    Sdb_StoFree( p );
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

