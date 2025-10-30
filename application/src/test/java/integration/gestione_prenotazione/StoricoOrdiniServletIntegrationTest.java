package integration.gestione_prenotazione;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.sottosistemi.gestione_prenotazione.view.StoricoOrdiniServlet;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import unit.test_DAO.DatabaseSetupForTest;

import java.lang.reflect.Method;
import java.sql.Connection;

import static org.mockito.Mockito.*;

public class StoricoOrdiniServletIntegrationTest {
    private StoricoOrdiniServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeAll
    static void setUpDatabase() throws Exception {
        DatabaseSetupForTest.configureH2DataSource();
        try (Connection conn = DataSourceSingleton.getInstance().getConnection()) {
            conn.createStatement().execute("SET REFERENTIAL_INTEGRITY FALSE");
            conn.createStatement().execute("DELETE FROM prenotazione");
            conn.createStatement().execute("DELETE FROM proiezione");
            conn.createStatement().execute("DELETE FROM slot");
            conn.createStatement().execute("DELETE FROM sala");
            conn.createStatement().execute("DELETE FROM film");
            conn.createStatement().execute("DELETE FROM sede");
            conn.createStatement().execute("DELETE FROM utente");
            conn.createStatement().execute("DELETE FROM cliente");
            conn.createStatement().execute("SET REFERENTIAL_INTEGRITY TRUE");
            conn.createStatement().execute("""
            INSERT INTO utente (email, password, ruolo) VALUES ('test@test.com', 'password', 'cliente');
            INSERT INTO cliente (email, nome, cognome) VALUES ('test@test.com', 'Mario', 'Rossi');
            INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Sede Test', 'Via Roma', 'Roma', '00100');
            INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);
            INSERT INTO film (id, titolo, genere, classificazione, durata, descrizione, is_proiettato) 
                VALUES (1, 'Film di Test', 'Azione', 'T', 120, 'Descrizione del film', TRUE);
            INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');
            INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) 
                VALUES (1, '2025-01-01', 1, 1, 1);
            INSERT INTO prenotazione (id, email_cliente, id_proiezione) 
                VALUES (1, 'test@test.com', 1);
        """);
        }
    }

    @BeforeEach
    void setUp() {
        servlet = new StoricoOrdiniServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        when(request.getSession()).thenReturn(session);
    }

    @Test
    void testDoGetSuccess() throws Exception {
        Cliente cliente = new Cliente();
        cliente.setEmail("test@test.com");
        cliente.setNome("Mario");
        cliente.setCognome("Rossi");
        when(session.getAttribute("cliente")).thenReturn(cliente);
        when(request.getRequestDispatcher("/WEB-INF/jsp/storicoOrdini.jsp")).thenReturn(dispatcher);
        System.out.println("Testing doGet with valid cliente:");
        System.out.println("Cliente Email: " + cliente.getEmail());
        System.out.println("Cliente Nome: " + cliente.getNome());
        System.out.println("Cliente Cognome: " + cliente.getCognome());
        Method doGetMethod = StoricoOrdiniServlet.class.getDeclaredMethod("doGet", HttpServletRequest.class, HttpServletResponse.class);
        doGetMethod.setAccessible(true);
        doGetMethod.invoke(servlet, request, response);
        verify(request).setAttribute(eq("storico"), anyList());
        verify(dispatcher).forward(request, response);
        System.out.println("Forward corretto verso la pagina di visualizzazione degli ordini");
    }

    @Test
    void testDoGetNoClienteInSession() throws Exception {
        when(session.getAttribute("cliente")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);
        System.out.println("Sessione con session.getAttribute(\"cliente\")=null");
        Method doGetMethod = StoricoOrdiniServlet.class.getDeclaredMethod("doGet", HttpServletRequest.class, HttpServletResponse.class);
        doGetMethod.setAccessible(true);
        doGetMethod.invoke(servlet, request, response);
        verify(request).setAttribute(eq("errorMessage"), eq("Cliente non trovato nella sessione."));
        verify(dispatcher).forward(request, response);
        System.out.println("Corretto forward verso la pagina di errore");
    }

    @Test
    void testDoGetExceptionHandling() throws Exception {
        when(session.getAttribute("cliente")).thenThrow(new RuntimeException("Test Exception"));
        when(request.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcher);
        Method doGetMethod = StoricoOrdiniServlet.class.getDeclaredMethod("doGet", HttpServletRequest.class, HttpServletResponse.class);
        doGetMethod.setAccessible(true);
        doGetMethod.invoke(servlet, request, response);
        verify(request).setAttribute(eq("errorMessage"), eq("Si è verificato un errore durante il recupero dello storico ordini."));
        verify(dispatcher).forward(request, response);
        System.out.println("Corretto forward verso la pagina di errore");
    }
}
