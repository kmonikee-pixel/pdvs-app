# PDVs Seda de Favela

App instalável (PWA) para a equipe de rua controlar pontos de venda, pedidos, visitas, reposição, ranking e bonificação.

- Endereço: https://app.sedadefavela.com.br
- Dados: Firebase (Firestore), com cache offline no aparelho. Nada de cliente fica neste repositório.
- Login: Firebase Authentication (e-mail e senha). Quem pode entrar é definido na tela Equipe do app.

## Arquivos
- `index.html`, `app.js`: o app
- `config.js`: configuração pública do Firebase e e-mail da administradora
- `sw.js`, `manifest.webmanifest`, ícones: instalação e funcionamento offline
- `firestore.rules`: regras de segurança. Ao mudar, copiar o conteúdo para Firebase > Firestore > Regras > Publicar.
