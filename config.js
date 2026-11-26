// Configuração do Firebase do projeto PDVs Seda de Favela.
// Estes dados não são senha: o Firebase foi feito para eles ficarem no app.
// Quem protege os dados são as regras de segurança (firestore.rules) e o login.
export const firebaseConfig = {
  apiKey: "AIzaSyAgRHyPg6erLMSrE8QBzeLv3NBqoChObHQ",
  authDomain: "pdvs-seda-de-favela.firebaseapp.com",
  projectId: "pdvs-seda-de-favela",
  storageBucket: "pdvs-seda-de-favela.firebasestorage.app",
  messagingSenderId: "768941520559",
  appId: "1:768941520559:web:19f4da15638d588e14065a"
};

// E-mail da administradora: tem acesso total, mesmo antes de existir a lista de equipe.
export const ADMIN_EMAIL = "sedadefavela@gmail.com";
