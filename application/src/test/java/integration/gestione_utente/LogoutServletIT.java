package integration.gestione_utente;

import integration.BaseIT;
import it.unisa.application.sottosistemi.gestione_utente.view.LogoutServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;

import java.io.IOException;

import static org.mockito.Mockito.*;

public class LogoutServletIT extends BaseIT {

    public static class TestableLogoutServlet extends LogoutServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp)
                throws ServletException, IOException {
            super.doGet(req, resp);
        }
    }

    private TestableLogoutServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setup() throws ServletException {
        servlet = new TestableLogoutServlet();
        servlet.init();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    @RepeatedTest(5)
    void testLogout_forwardsToHome() throws ServletException, IOException {
        // sessione mockata
        when(request.getSession()).thenReturn(session);

        when(request.getRequestDispatcher("/Home")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(session, times(1)).invalidate();
        verify(dispatcher).forward(request, response);
    }
}
